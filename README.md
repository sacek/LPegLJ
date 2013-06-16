LPegLJ
======

LPeg Parser in pure LuaJIT  
(straight Lua + FFI translation of LPeg C code)   
based on LPeg v.12 - PEG pattern matching for Lua  
Lua.org & PUC-Rio  written by Roberto Ierusalimschy  
http://www.inf.puc-rio.br/~roberto/lpeg/  

*Usage:  

local lpeglj = require"lpeglj"  
local pattern = lpeglj.P("a")    
lpeglj.match(pattern, "a")    
or  
pattern:match("a")  

*Compatibility:

-full syntactical and functional compatibility with LPeg v.12   
-need LuaJIT 2.x  

*Diferences from LPeg v.12:

Input parameter (subject string) for match function can be string or table with defined
functions len and sub (is possible use coroutine.yield for input data).
