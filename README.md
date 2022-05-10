# This is a port to LjsJIT https://github.com/mingodad/ljsjit

LPegLJ v1.0
=============

LPeg Parser in pure LuaJIT  
(straight Lua + FFI translation of LPeg C code)   
based on LPeg v1.0 - PEG pattern matching for Lua  
Lua.org & PUC-Rio  written by Roberto Ierusalimschy  
http://www.inf.puc-rio.br/~roberto/lpeg/

left recursion support is based on Sérgio Medeiros algorithm
http://arxiv.org/abs/1207.0443

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

- full syntactical and functional backward compatibility with LPeg v1.0
- works only with LuaJIT 2.x  

### Differences from LPeg v1.0:

Description in doc/USAGE.md

- LPegLJ supports direct and indirect left recursion based on Sérgio Medeiros algorithm (http://arxiv.org/abs/1207.0443)
- patterns can be saved and loaded
- supports memoization (restricted) - useful for complex grammars
- can be used in stream mode (infinite parsing)
- VM action runtime listing (tracing) for debugging purposes
