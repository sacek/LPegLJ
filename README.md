LPegLJ
======

LPeg version 0.12 Parser in pure LuaJIT
https://github.com/sacek/LPegLJ/

LPeg Parser in LuaJIT
based on LPeg v0.12 - PEG pattern matching for Lua
Lua.org & PUC-Rio  written by Roberto Ierusalimschy
http://www.inf.puc-rio.br/~roberto/lpeg/

*Usage:

local lpeglj = require"lpeglj"

local pattern = lpeglj.P("a")
lpeglj.match(pattern, "a")
or
pattern:match("a")

*Compatibility:
Need LuaJIT 2.x

*Diferences from LPEG:

Because patterns in LPegLJ are standard tables (not userdata) # prefix (for positive look-ahead pattern) not work (in Lua 5.1).
#prefix (positive look-ahead) should be replaced by L(pattern) or you can use LuaJIT compiled with
Lua 5.2 compability flag (LUAJIT_ENABLE_LUA52COMPAT)

