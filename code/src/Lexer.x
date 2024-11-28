{
module Lexer where
}

%wrapper  "basic"

-- Literals
$digit = [ 0-9 ]
@posInt = $digit+

-- Identifiers
$lower = [ a-z ]
$upper = [ A-Z ]
@lowerId = $lower [ $lower $upper $digit _ ' ]*
@upperId = $upper [ $lower $upper $digit _ ' ]*

tokens :-
$white+          ;
("\" | "λ")      { const TkBackslash }
("->" | "→")     { const TkArrow }
("=>" | "⇒")    { const TkDoubleArrow }
("rec" | "μ")    { const TkRec }
("forall" | "∀") { const TkForall }
("exists" | "∃") { const TkExists }
":"              { const TkColon }
"."              { const TkDot }
"@"              { const TkAt }
","              { const TkComma }
"("              { const TkLParen }
")"              { const TkRParen }
"{"              { const TkLBrace }
"}"              { const TkRBrace }
"<"              { const TkLT }
">"              { const TkGT }
"["              { const TkLSquare }
"]"              { const TkRSquare }
";"              { const TkSemi }
("+" | "⊕")      { const TkPlus }
"&"              { const TkAmp }
"!"              { const TkBang }
"?"              { const TkQuestion }
"Int"            { const TkInt }
"Skip"           { const TkSkip }
"Close"          { const TkClose }
"Wait"           { const TkWait }
"Dual"           { const TkDual }
"S"              { const TkS }
"T"              { const TkT }
@posInt          { TkVar . read }

{
data Token 
  = TkForall
  | TkExists
  | TkRec
  | TkBackslash
  | TkArrow 
  | TkColon 
  | TkDot
  | TkComma 
  | TkLParen
  | TkRParen 
  | TkLBrace
  | TkRBrace
  | TkSemi 
  | TkPlus 
  | TkStar 
  | TkGT 
  | TkLT 
  | TkInt
  | TkDual 
  | TkSkip 
  | TkClose 
  | TkWait 
  | TkBang
  | TkQuestion
  | TkAmp
  | TkT
  | TkS
  | TkDoubleArrow
  | TkVar Int
  | TkAt
  | TkLSquare 
  | TkRSquare
  deriving (Eq, Show)

-- main = do
--   s <- getContents
--   print (alexScanTokens s)
}