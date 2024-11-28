{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Read where

import Lexer
import Parser
import Syntax

instance Read Type where
    readsPrec _ = (:[]) . (,"") . parseType . alexScanTokens

instance Read Kind where
    readsPrec _ = (:[]) . (,"") . parseKind . alexScanTokens

instance Read BaseKind where
    readsPrec _ = (:[]) . (,"") . parseBaseKind . alexScanTokens