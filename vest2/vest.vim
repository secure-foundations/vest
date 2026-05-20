
" Quit if a syntax file was already loaded
if exists("b:current_syntax")
  finish
endif

" Define syntax for comments
syntax match vestComment "//.*$"
highlight link vestComment Comment

" Define syntax for keywords
syntax keyword vestKeyword const let wrap choose apply Option Vec Vec1 Tail secret enum
highlight link vestKeyword Keyword

syntax keyword vestPrimitiveType u8 u16 u32 u64
highlight link vestPrimitiveType Type

" var_id: Lowercase letters followed by digits, lowercase, or underscores
syntax match vestVarId "\<\l\(\l\|\d\|_\)*\>"
highlight link vestVarId Identifier

" const_id: Uppercase letters possibly followed by more uppercase or underscores
syntax match vestConstId "\<\u\(\u\|_\)*\>"
highlight link vestConstId Constant

" choice_id: Uppercase letters followed by any letters, digits, or underscores
syntax match vestChoiceId "\<\u\(\w\|_\)*\>"
highlight link vestChoiceId Type

" stream_id: Dollar sign followed by lowercase and possibly digits, lowercase, or underscores
syntax match vestStreamId "\$\<\l\(\l\|\d\|_\)*\>"
highlight link vestStreamId PreProc

" depend_id: At sign followed by lowercase and possibly digits, lowercase, or underscores
syntax match vestDependId "@\<\l\(\l\|\d\|_\)*\>"
highlight link vestDependId PreProc

" Define syntax for special characters and operators
syntax match vestSpecialChar "[\[\]{}()<>,.;:=|]"
highlight link vestSpecialChar SpecialChar

" Define syntax for numbers
syntax match vestNumber "\<\d\+\>"
highlight link vestNumber Number

" Define syntax for hex numbers
syntax match vestHexNumber "\<0x\x\+\>"
highlight link vestHexNumber Number

" Define syntax for ASCII characters
syntax match vestASCII "'\\x\x\{2}'"
highlight link vestASCII String

" Define syntax for string literals
syntax match vestString '"[^"]*"'
highlight link vestString String

" Define syntax for char literals
syntax match vestChar "'[^']'"
highlight link vestChar String

" forbidden keywords (rust reserved keywords except for `enum`, `const`, and `let`)
syntax keyword vestForbidden abstract alignof as become box break continue crate do else extern false
      \ final fn for if impl in loop macro match mod move mut offsetof override priv proc pure pub ref return
      \ Self self sizeof static struct super trait true type typeof unsafe unsized use virtual where while yield 
highlight default link vestForbidden Error
" Set the syntax type
let b:current_syntax = "vest"
