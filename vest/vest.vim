" Vim syntax file for the Vest DSL
" Language: Vest
" Upstream: https://github.com/secure-foundations/vest
"
" Kept in sync with the PEG grammar in vest/src/vest.pest.  When that file
" changes, re-check the keyword, type, and operator lists below.
"
" Install by copying to ~/.vim/syntax/vest.vim (or
" ~/.config/nvim/syntax/vest.vim) and adding:
"   autocmd BufRead,BufNewFile *.vest setfiletype vest

if exists("b:current_syntax")
  finish
endif

" --------------------------------------------------------------------------
" Keywords and built-in formats
"
" These are exactly the `reserved_word` rule in vest.pest, split into
" statement-level keywords and format names, plus `bits`, which is a literal in
" `bits_combinator` rather than a reserved word.
" --------------------------------------------------------------------------
syntax keyword vestKeyword const enum choose wrap macro bits

syntax keyword vestType Option Vec Tail Nothing Never
syntax match   vestType "\<\%(btc_varint\|uleb128\)\>"
" `int_combinator`: (u|i) followed by an arbitrary bit width, e.g. u8, u24, i64.
syntax match   vestType "\<[ui]\d\+\>"

" --------------------------------------------------------------------------
" Identifiers with dedicated syntax
" --------------------------------------------------------------------------
" `depend_id`: @field, @outer.inner
syntax match vestDependId "@\h\w*\%(\.\h\w*\)*"

" `macro_invocation`: name!(..)
syntax match vestMacro "\<\h\w*\ze!("

" `variant_id` wildcard arm in `choose`
syntax match vestWildcard "\<_\>"

" `combinator_defn` / `const_combinator_defn` name in the first column.  This is
" a heuristic: enum fields share the `name = value` shape but are indented.
syntax match vestDefinition "^\h\w*\ze\s*\%((\_[^)]*)\)\?\s*="

" --------------------------------------------------------------------------
" Literals
" --------------------------------------------------------------------------
" `typed_const_int`: an optional u<width>/i<width> suffix on a literal.
syntax match vestNumber "\<0x\x\+\%([ui]\d\+\)\?\>"
syntax match vestNumber "\<\d\+\%([ui]\d\+\)\?\>"

" `ascii`: '\x1b' or 'a'
syntax match  vestChar   "'\%(\\x\x\{2}\|[^']\)'"
" `const_char_array`.  The grammar does not forbid a newline inside the quotes,
" but `oneline` keeps an unterminated quote from colouring the rest of the file.
syntax region vestString start=+"+ end=+"+ oneline

" --------------------------------------------------------------------------
" Punctuation, operators, and directives
"
" Order matters here.  When two items match at the same position Vim keeps the
" one defined last, so the broad single-character class comes first and the
" specific multi-character forms that start with the same characters follow it.
" --------------------------------------------------------------------------
syntax match vestDelimiter "[[\]{}()<>,;:=|!+*/-]"

" >>= dependent combinator, => choice arm, ... non-exhaustive marker,
" .. constraint range.
syntax match vestOperator ">>=\|=>\|\.\.\.\|\.\."

" `size_expr`: |format| yields the static byte size of a format.
syntax match vestSizeExpr "|\s*\%(\h\w*\|[ui]\d\+\|btc_varint\|uleb128\)\s*|"

" `endianess_defn`
syntax match vestDirective "!\%(LITTLE\|BIG\)_ENDIAN\>"

" --------------------------------------------------------------------------
" Rust keywords that the Vest grammar accepts as identifiers but that produce
" Rust which does not compile.  Highlighted as errors so the problem surfaces
" in the .vest file rather than in the generated .rs file.
" --------------------------------------------------------------------------
syntax keyword vestForbidden as async await break continue crate dyn else
      \ extern false fn for if impl in let loop match mod move mut pub ref
      \ return self Self static struct super trait true type unsafe use where
      \ while abstract become box do final override priv try typeof unsized
      \ virtual yield

" --------------------------------------------------------------------------
" Comments are defined last on purpose: Vim resolves items that match at the
" same position in favour of the one defined last, and `vestDelimiter` also
" matches the `/` that opens a comment.
" --------------------------------------------------------------------------
syntax keyword vestTodo contained TODO FIXME XXX NOTE
syntax match   vestComment "//.*$" contains=vestTodo

" --------------------------------------------------------------------------
" Highlight groups
" --------------------------------------------------------------------------
highlight default link vestComment    Comment
highlight default link vestTodo       Todo
highlight default link vestDirective  PreProc
highlight default link vestKeyword    Keyword
highlight default link vestType       Type
highlight default link vestDependId   Identifier
highlight default link vestMacro      Macro
highlight default link vestDefinition Function
highlight default link vestWildcard   Special
highlight default link vestSizeExpr   Special
highlight default link vestNumber     Number
highlight default link vestChar       Character
highlight default link vestString     String
highlight default link vestOperator   Operator
highlight default link vestDelimiter  Delimiter
highlight default link vestForbidden  Error

let b:current_syntax = "vest"
