{
module Parser where 

import Lexer
import Syntax

import qualified Data.Map as Map

}

%name parseType Type
%name parseKind Kind 
%name parseBaseKind BaseKind
%tokentype { Token }

%token  
    'forall' { TkForall }
    'exists' { TkExists }
    'rec'    { TkRec }
    '@'      { TkAt }
    '\\'     { TkBackslash }
    '->'     { TkArrow }
    ':'      { TkColon }
    '.'      { TkDot }
    ','      { TkComma }
    '('      { TkLParen }
    ')'      { TkRParen }
    '{'      { TkLBrace }
    '}'      { TkRBrace }
    ';'      { TkSemi }
    '+'      { TkPlus }
    '>'      { TkGT }
    '<'      { TkLT }
    'Int'    { TkInt }
    'Dual'   { TkDual }
    'Skip'   { TkSkip }
    'Close'  { TkClose }
    'Wait'   { TkWait }
    '!'      { TkBang }
    '?'      { TkQuestion }
    '&'      { TkAmp }
    'T'      { TkT }
    'S'      { TkS }
    '=>'     { TkDoubleArrow }
    VAR      { TkVar $$ }

%right    '.'
%right    '=>' '->' ARROW
%right    ';' SEMI
%right    MSG

%%

Kind :: { Kind }
Kind : KindPrimary { $1 }
     | Kind '=>' Kind { ArrowK $1 $3 }

KindPrimary :: {Kind}
KindPrimary : BaseKind { ProperK $1 }
            | '(' Kind ')' { $2 }

BaseKind :: { BaseKind }
BaseKind : 'S' { Session }
         | 'T' { Top } 

TypePrimary :: { Type }
TypePrimary : 'Int'    { Int }
            | '(' Arrow ')'    { $2 }
            | '{' LabelTypeListComma '}' { Labelled Record $2 }
            | '<' LabelTypeListComma '>' { Labelled Variant $2 }
            | 'rec' '@' BaseKind { Rec $3 }
            | Quantifier '@' KindPrimary '@' KindPrimary { Quantifier $1 $3 $5 }
            | 'Skip'   { Skip }
            | 'Close'  { End Out }
            | 'Wait'   { End In }
            | '(' Message ')' { $2 }
            | '(' ';' ')'        { Semi }
            | View '{' LabelTypeListComma '}'     { Choice $1 $3 }
            | 'Dual'   { Dual }
            | VAR { Var $1 }
            | '(' Type ')' { $2 }

Arrow :: { Type }
Arrow : '->' '@' BaseKind '@' BaseKind { Arrow $3 $5 }

Quantifier :: { Polarity }
Quantifier : 'forall' { Out }
           | 'exists' { In }

Message :: { Type }
Message : Polarity '@' BaseKind { Message $1 $3 }

Type :: { Type }
  : Type Arrow Type %prec ARROW { App (App $2 $1) $3 }
  | Type ';' Type               { App (App Semi $1) $3 }
  | Message Type %prec MSG      { App $1 $2 }
  | '\\' KindedVarListWS '.' Type   { foldr (uncurry Abs) $4 $2 }
  | TypeApp                     { $1 }

TypeApp :: { Type }
  : TypeApp TypePrimary { App $1 $2 }
  | TypePrimary { $1 }

Polarity :: { Polarity }
  : '!'  { Out }
  | '?'  { In }

View :: { View }
  : '+' { Internal }
  | '&' { External }

LabelTypeListComma :: { Map.Map Variable Type }
LabelTypeListComma : {- empty -}          { Map.empty }
                   | NELabelTypeListComma { $1 }

NELabelTypeListComma :: { Map.Map Variable Type }
  : VAR ':' Type ',' NELabelTypeListComma { Map.insert $1 $3 $5 }
  | VAR ':' Type { Map.singleton $1 $3 }

KindedVarListWS :: { [(Variable, Kind)] }
  : {- empty -} { [] }
  | KindedVar KindedVarListWS { $1 : $2 }

KindedVar :: { (Variable, Kind) }
  : VAR ':' Kind { ($1, $3) }

{
happyError tks = error ("Parse error on input: "++show tks)
}