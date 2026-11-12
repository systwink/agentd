

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#define MAX_PROCS    256
#define MIN_UPTIME   10    /* seconds a child must live to count as "healthy" */
#define MAX_BACKOFF  300   /* seconds */
#define KILL_GRACE   5     /* seconds between SIGTERM and SIGKILL */

typedef struct {
    int    used;
    char   path[PATH_MAX];
    pid_t  pid;            /* 0 when not running */
    time_t started;
    time_t next_start;     /* earliest time we may (re)start it */
    int    backoff;        /* current backoff in seconds */
    time_t mtime;          /* mtime of the binary when we last saw it */
    int    seen;           /* scan marker */
    int    removed;        /* file vanished; free slot once child is gone */
    int    restart;        /* file changed; restart immediately after exit */
    time_t kill_deadline;  /* when to escalate SIGTERM -> SIGKILL (0 = none) */
} Proc;

static Proc procs[MAX_PROCS];
static const char *watch_dir;
static int strict;   /* set when running as root: enforce ownership checks */

/* Remember rejected files so we log each one once, not on every scan. */
#define MAX_REJECTS 64
static struct { char path[PATH_MAX]; time_t mtime; } rejects[MAX_REJECTS];

static volatile sig_atomic_t g_stop   = 0;
static volatile sig_atomic_t g_reload = 0;

static void on_signal(int sig)
{
    if (sig == SIGHUP) g_reload = 1;
    else               g_stop = 1;
}

static void logmsg(const char *fmt, ...)
{
    char ts[32];
    time_t now = time(NULL);
    struct tm tm;
    localtime_r(&now, &tm);
    strftime(ts, sizeof ts, "%Y-%m-%d %H:%M:%S", &tm);

    fprintf(stderr, "%s agentd[%d]: ", ts, (int)getpid());
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fputc('\n', stderr);
    fflush(stderr);
}

static void reject_once(const char *path, time_t mtime, const char *why)
{
    int free_i = -1;
    for (int i = 0; i < MAX_REJECTS; i++) {
        if (rejects[i].path[0] == '\0') { if (free_i < 0) free_i = i; continue; }
        if (strcmp(rejects[i].path, path) == 0) {
            if (rejects[i].mtime == mtime) return;
            rejects[i].mtime = mtime;
            logmsg("refusing %s: %s", path, why);
            return;
        }
    }
    if (free_i >= 0) {
        snprintf(rejects[free_i].path, PATH_MAX, "%s", path);
        rejects[free_i].mtime = mtime;
    }
    logmsg("refusing %s: %s", path, why);
}

static Proc *find_by_path(const char *path)
{
    for (int i = 0; i < MAX_PROCS; i++)
        if (procs[i].used && strcmp(procs[i].path, path) == 0)
            return &procs[i];
    return NULL;
}

static Proc *find_by_pid(pid_t pid)
{
    for (int i = 0; i < MAX_PROCS; i++)
        if (procs[i].used && procs[i].pid == pid)
            return &procs[i];
    return NULL;
}

static Proc *alloc_slot(void)
{
    for (int i = 0; i < MAX_PROCS; i++)
        if (!procs[i].used) {
            memset(&procs[i], 0, sizeof procs[i]);
            procs[i].used = 1;
            return &procs[i];
        }
    return NULL;
}

static void stop_proc(Proc *p)
{
    if (p->pid > 0) {
        logmsg("stopping %s (pid %d)", p->path, (int)p->pid);
        kill(p->pid, SIGTERM);
        p->kill_deadline = time(NULL) + KILL_GRACE;
    }
}

static void start_proc(Proc *p)
{
    pid_t pid = fork();
    if (pid < 0) {
        logmsg("fork failed for %s: %s", p->path, strerror(errno));
        p->next_start = time(NULL) + 5;
        return;
    }

    if (pid == 0) {
        /* child */
        sigset_t empty;
        sigemptyset(&empty);
        sigprocmask(SIG_SETMASK, &empty, NULL);

        signal(SIGHUP,  SIG_DFL);
        signal(SIGINT,  SIG_DFL);
        signal(SIGTERM, SIG_DFL);

        int devnull = open("/dev/null", O_RDWR);
        if (devnull >= 0) {
            dup2(devnull, STDIN_FILENO);
            if (devnull > STDERR_FILENO) close(devnull);
        }
        if (chdir(watch_dir) != 0) { /* non-fatal */ }

        execl(p->path, p->path, (char *)NULL);
        fprintf(stderr, "agentd: exec %s failed: %s\n", p->path, strerror(errno));
        _exit(127);
    }

    p->pid = pid;
    p->started = time(NULL);
    p->kill_deadline = 0;
    logmsg("started %s (pid %d)", p->path, (int)pid);
}

static void scan_dir(void)
{
    for (int i = 0; i < MAX_PROCS; i++) procs[i].seen = 0;

    DIR *d = opendir(watch_dir);
    if (!d) {
        logmsg("cannot open %s: %s", watch_dir, strerror(errno));
        return;
    }

    struct dirent *e;
    while ((e = readdir(d)) != NULL) {
        if (e->d_name[0] == '.') continue;

        char path[PATH_MAX];
        if (snprintf(path, sizeof path, "%s/%s", watch_dir, e->d_name) >= (int)sizeof path)
            continue;

        struct stat st;
        if (lstat(path, &st) != 0) continue;
        if (!S_ISREG(st.st_mode) || !(st.st_mode & S_IXUSR)) continue;

        if (strict) {
            if (st.st_uid != 0) {
                reject_once(path, st.st_mtime, "not owned by root");
                continue;
            }
            if (st.st_mode & (S_IWGRP | S_IWOTH)) {
                reject_once(path, st.st_mtime, "writable by group/others");
                continue;
            }
        }

        Proc *p = find_by_path(path);
        if (!p) {
            p = alloc_slot();
            if (!p) { logmsg("too many programs, ignoring %s", path); continue; }
            snprintf(p->path, sizeof p->path, "%s", path);
            p->mtime = st.st_mtime;
            p->next_start = 0;
            logmsg("discovered %s", path);
        } else if (p->mtime != st.st_mtime) {
            p->mtime = st.st_mtime;
            p->backoff = 0;
            if (p->pid > 0) {
                logmsg("%s changed, restarting", path);
                p->restart = 1;
                stop_proc(p);
            } else {
                p->next_start = 0;
            }
        }
        p->seen = 1;
        p->removed = 0;
    }
    closedir(d);

    /* Anything we know about that wasn't seen has been deleted/disabled. */
    for (int i = 0; i < MAX_PROCS; i++) {
        Proc *p = &procs[i];
        if (!p->used || p->seen) continue;
        logmsg("%s is gone", p->path);
        if (p->pid > 0) {
            p->removed = 1;
            stop_proc(p);
        } else {
            p->used = 0;
        }
    }
}

static void reap_children(void)
{
    int status;
    pid_t pid;

    while ((pid = waitpid(-1, &status, WNOHANG)) > 0) {
        Proc *p = find_by_pid(pid);
        if (!p) continue;

        time_t now = time(NULL);
        long uptime = (long)(now - p->started);

        if (WIFEXITED(status))
            logmsg("%s exited with status %d after %lds", p->path, WEXITSTATUS(status), uptime);
        else if (WIFSIGNALED(status))
            logmsg("%s killed by signal %d after %lds", p->path, WTERMSIG(status), uptime);

        p->pid = 0;
        p->kill_deadline = 0;

        if (p->removed) {
            p->used = 0;
            continue;
        }
        if (p->restart) {
            p->restart = 0;
            p->backoff = 0;
            p->next_start = now;
            continue;
        }

        if (uptime < MIN_UPTIME) {
            p->backoff = p->backoff ? p->backoff * 2 : 1;
            if (p->backoff > MAX_BACKOFF) p->backoff = MAX_BACKOFF;
        } else {
            p->backoff = 0;
        }
        p->next_start = now + p->backoff;
        if (p->backoff)
            logmsg("will restart %s in %ds", p->path, p->backoff);
    }
}

static void tick(void)
{
    time_t now = time(NULL);
    for (int i = 0; i < MAX_PROCS; i++) {
        Proc *p = &procs[i];
        if (!p->used) continue;

        if (p->pid > 0 && p->kill_deadline && now >= p->kill_deadline) {
            logmsg("%s ignored SIGTERM, sending SIGKILL", p->path);
            kill(p->pid, SIGKILL);
            p->kill_deadline = 0;
        }
        if (p->pid == 0 && !p->removed && now >= p->next_start)
            start_proc(p);
    }
}

static void shutdown_all(void)
{
    logmsg("shutting down");
    for (int i = 0; i < MAX_PROCS; i++)
        if (procs[i].used && procs[i].pid > 0)
            kill(procs[i].pid, SIGTERM);

    for (int waited = 0; waited < KILL_GRACE * 10; waited++) {
        int alive = 0;
        for (int i = 0; i < MAX_PROCS; i++) {
            Proc *p = &procs[i];
            if (!p->used || p->pid <= 0) continue;
            if (waitpid(p->pid, NULL, WNOHANG) == p->pid) p->pid = 0;
            else alive++;
        }
        if (!alive) return;
        usleep(100000);
    }
    for (int i = 0; i < MAX_PROCS; i++)
        if (procs[i].used && procs[i].pid > 0) {
            kill(procs[i].pid, SIGKILL);
            waitpid(procs[i].pid, NULL, 0);
        }
}

int main(int argc, char **argv)
{
    if (argc < 2 || argc > 3) {
        fprintf(stderr, "usage: %s <directory> [scan_interval_seconds]\n", argv[0]);
        return 64;
    }

    static char dir_buf[PATH_MAX];
    strict = (geteuid() == 0);
    watch_dir = argv[1];
    if (strict && watch_dir[0] == '~') {
        fprintf(stderr, "running as root: use an absolute path, not ~\n");
        return 64;
    }
    if (watch_dir[0] == '~' && (watch_dir[1] == '/' || watch_dir[1] == '\0')) {
        const char *home = getenv("HOME");
        if (!home) {
            fprintf(stderr, "HOME is not set, cannot expand ~\n");
            return 78;
        }
        snprintf(dir_buf, sizeof dir_buf, "%s%s", home, watch_dir + 1);
        watch_dir = dir_buf;
    }
    if (!strict)
        mkdir(watch_dir, 0755);   /* never create dirs as root inside a user's home */

    int interval = (argc == 3) ? atoi(argv[2]) : 5;
    if (interval < 1) interval = 5;

    struct stat st;
    if (stat(watch_dir, &st) != 0 || !S_ISDIR(st.st_mode)) {
        fprintf(stderr, "%s: not a directory\n", watch_dir);
        return 66;
    }

    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_signal;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGTERM, &sa, NULL);
    sigaction(SIGINT,  &sa, NULL);
    sigaction(SIGHUP,  &sa, NULL);

    logmsg("watching %s (scan every %ds)%s", watch_dir, interval,
           strict ? ", running as root: only root-owned, non-writable files will run" : "");

    time_t next_scan = 0;
    while (!g_stop) {
        time_t now = time(NULL);
        if (g_reload || now >= next_scan) {
            g_reload = 0;
            scan_dir();
            next_scan = now + interval;
        }
        reap_children();
        tick();

        struct timespec ts = { 1, 0 };   /* interrupted early by signals */
        nanosleep(&ts, NULL);
    }

    shutdown_all();
    return 0;
}
