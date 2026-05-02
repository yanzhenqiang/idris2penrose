module RTS where
import Base

-- Runtime system generation: C backend and WebAssembly C backend.

cHeader :: String
cHeader = unlines
  [ "#include <stdio.h>"
  , "#include <stdlib.h>"
  , "#include <string.h>"
  , "#include <time.h>"
  , ""
  , "typedef unsigned u;"
  , "enum { TOP = 1<<23, BUFMAX = 1<<20 };"
  , "u *mem, *altmem, *sp, *spTop, hp;"
  , "enum { FORWARD = 27, REDUCING = 9 };"
  , ""
  , "static inline u isAddr(u n) { return n>=128; }"
  , ""
  , "void gc() {"
  , "  u di = 128; hp = 128;"
  , "  sp = altmem + TOP - 1;"
  , "  // placeholder: full GC would evacuate reachable nodes"
  , "}"
  , ""
  , "static inline u app(u f, u x) {"
  , "  mem[hp] = f; mem[hp+1] = x; hp += 2; return hp-2;"
  , "}"
  , ""
  , "void run(u root) {"
  , "  mem = malloc(TOP * sizeof(u));"
  , "  altmem = malloc(TOP * sizeof(u));"
  , "  spTop = mem + TOP - 1;"
  , "  hp = 128;"
  , "  sp = spTop;"
  , "  *sp = app(root, 0);"
  , "  printf(\"Execution stub.\\n\");"
  , "}"
  , ""
  , "int main(int argc, char **argv) {"
  , "  return 0;"
  , "}"
  ]

-- WebAssembly C backend (freestanding).
wasify :: String -> String
wasify c = "#include <stddef.h>\n" ++
  "#include <stdint.h>\n" ++
  "typedef uint32_t u;\n" ++
  "enum { TOP = 1<<20 };\n" ++
  "static u mem[TOP];\n" ++
  "static u hp = 128;\n" ++
  "static inline u app(u f, u x) { mem[hp]=f; mem[hp+1]=x; hp+=2; return hp-2; }\n" ++
  "__attribute__((export_name(\"run\"))) void run(void) { hp = 128; }\n" ++
  c

-- Raw combinator memory dump format.
outputC :: String -> String
outputC body = cHeader ++ "\n/* User program */\n" ++ body

outputRaw :: String -> String
outputRaw s = "# raw memory dump\n" ++ s

outputWasmC :: String -> String
outputWasmC body = wasify body

-- Encode combinators for raw dump.
encodeComb "Y" = 1
encodeComb "S" = 2
encodeComb "K" = 3
encodeComb "I" = 4
encodeComb "B" = 5
encodeComb "C" = 6
encodeComb "T" = 7
encodeComb "R" = 8
encodeComb "F" = 9
encodeComb "+" = 10
encodeComb "-" = 11
encodeComb "*" = 12
encodeComb "/" = 13
encodeComb "%" = 14
encodeComb "=" = 15
encodeComb "L" = 16
encodeComb ":" = 17
encodeComb "a" = 18
encodeComb _ = 0
