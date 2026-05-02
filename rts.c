#include <stdio.h>
#include <stdlib.h>

static int env_argc;
static char **env_argv;

int getargcount() { return env_argc; }
int getargchar(int n, int k) { return env_argv[n][k]; }

static int nextCh, isAhead;

int eof_shim() {
  if (!isAhead) {
    isAhead = 1;
    nextCh = getchar();
  }
  return nextCh == -1;
}

void exit(int);
void putchar_shim(int c) { putchar(c); }
int getchar_shim() {
  if (!isAhead) nextCh = getchar();
  if (nextCh == -1) exit(1);
  isAhead = 0;
  return nextCh;
}
void errchar(int c) { fputc(c, stderr); }
void errexit() { fputc('\n', stderr); }

void rts_init(int argc, char **argv) {
  env_argc = argc;
  env_argv = argv;
}
