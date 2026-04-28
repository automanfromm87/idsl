" Vim syntax file for iDSL.
"
" The LSP server emits semantic tokens that supersede this file once
" the buffer attaches; this baseline gives reasonable highlighting
" before / outside the LSP.

if exists('b:current_syntax')
  finish
endif

" ---------- comments ----------
syntax match  idslComment  "#.*$"

" ---------- strings ----------
" Triple-quoted strings (rule descriptions) come first so they win
" over regular doubles.
syntax region idslTString  start='"""' end='"""'
syntax region idslString   start='"' end='"' skip='\\"'

" ---------- numbers / dates / money ----------
syntax match idslMoney    "\$[0-9][0-9,]*\(\.[0-9]\+\)\?"
syntax match idslDate     "\<[0-9]\{4}-[0-9]\{2}-[0-9]\{2}\>"
syntax match idslNumber   "\<[0-9]\+\(\.[0-9]\+\)\?\>"

" ---------- keywords ----------
syntax keyword idslDecl    schema rule test instance action include
syntax keyword idslDecl    domain predicate
syntax keyword idslBlock   when then given expect cases on priority
syntax keyword idslCtrl    if else
syntax keyword idslLogic   and or not is missing present
syntax keyword idslIter    any every count sum of in where for
syntax keyword idslBuiltin min max
syntax keyword idslSelf    self
syntax keyword idslDefault default
syntax keyword idslBool    true false

" ---------- metadata (`@version`, `@status`, `@action`, …) ----------
syntax match idslMeta     "@[A-Za-z_][A-Za-z0-9_]*"

" ---------- operators ----------
syntax match idslArrow    "->"
syntax match idslOp       "==\|!=\|<=\|>=\|[+\-*/<>=]"

" ---------- highlight links ----------
hi def link idslComment   Comment
hi def link idslTString   String
hi def link idslString    String
hi def link idslMoney     Number
hi def link idslDate      Number
hi def link idslNumber    Number

hi def link idslDecl      Keyword
hi def link idslBlock     Keyword
hi def link idslCtrl      Conditional
hi def link idslLogic     Operator
hi def link idslIter      Repeat
hi def link idslBuiltin   Function
hi def link idslSelf      Special
hi def link idslDefault   Keyword
hi def link idslBool      Boolean
hi def link idslMeta      PreProc
hi def link idslArrow     Operator
hi def link idslOp        Operator

let b:current_syntax = 'idsl'
