LPegLJ
======

LPeg version 0.12 Parser in pure LuaJIT
https://github.com/sacek/LPegLJ/

LPeg Parser in LuaJIT
based on LPeg v0.12 - PEG pattern matching for Lua
Lua.org & PUC-Rio  written by Roberto Ierusalimschy
http://www.inf.puc-rio.br/~roberto/lpeg/

### Usage:

```Lua
local lpeglj = require"lpeglj"

local pattern = lpeglj.P("a")

-- then:
lpeglj.match(pattern, "a")

-- or, equivalently:
pattern:match("a")
```

### Compatibility:
Need LuaJIT 2.x

### Diferences from LPEG:

The `#pattern` syntax relies on either the availability of 
`newproxy()` (present by default) or on the `LUAJIT_ENABLE_LUA52COMPAT` 
compile flag. If neither is present (in a restricted sandbox, 
for example), you can use `lpeg.L(pattern)` instead.
