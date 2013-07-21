LPegLJ
======

LPeg Parser in pure LuaJIT  
(straight Lua + FFI translation of LPeg C code)   
based on LPeg v.12 - PEG pattern matching for Lua  
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

- full syntactical and functional compatibility with LPeg v.12   
- need LuaJIT 2.x  

### Differences from LPeg v.12:

The `#pattern` syntax for lookaheds relies on either the availability of 
`newproxy()` (present by default) or on the `LUAJIT_ENABLE_LUA52COMPAT`
compile flag. If neither is present (in a restricted sandbox,
for example), you can use `lpeglj.L(pattern)` instead.
