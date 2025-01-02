module CExprSpec where
import           Test.Hspec
import CExpr
import CType

testCExpr = do
  let testv = Const int32 22
  describe "typeOf" $ do
    it "const" $ do
      typeOf testv `shouldBe` int32
    it "Arg" $ do
      typeOf ( Arg  uint32 "D2" ) `shouldBe` uint32
    it "VarValue" $ do
      typeOf ( VarValue $ EnvVar uint32 "foo" ) `shouldBe` uint32
    it "VarAddr" $ do
      typeOf ( VarAddr $ EnvVar uint32 "foo" ) `shouldBe` PTR uint32
    it "Cast" $ do
      typeOf ( Cast int16 testv ) `shouldBe` int16
    it "!" $ do
      typeOf ( Op1 "!" testv ) `shouldBe` BOOL
    it "~" $ do
      typeOf ( Op1 "~" testv ) `shouldBe` int32
    it "++" $ do
      typeOf ( IncDec False False $ EnvVar uint32 "test" ) `shouldBe` uint32
    it "&&" $ do
      typeOf ( Op2 testv "&&" testv ) `shouldBe` BOOL
    it "||" $ do
      typeOf ( Op2 testv "||" testv ) `shouldBe` BOOL
    it "<" $ do
      typeOf ( Op2 testv "<" testv ) `shouldBe` BOOL
    it "<=" $ do
      typeOf ( Op2 testv "<=" testv ) `shouldBe` BOOL
    it ">" $ do
      typeOf ( Op2 testv ">" testv ) `shouldBe` BOOL
    it ">=" $ do
      typeOf ( Op2 testv ">=" testv ) `shouldBe` BOOL
    it "==" $ do
      typeOf ( Op2 testv "==" testv ) `shouldBe` BOOL
    it "!=" $ do
      typeOf ( Op2 testv "!=" testv ) `shouldBe` BOOL
    it "+" $ do
      typeOf ( Op2 testv "+" testv ) `shouldBe` int32
    it "?:" $ do
      typeOf ( CondExpr testv testv testv ) `shouldBe` int32
    it "(,)" $ do
      typeOf ( Expr2 testv testv ) `shouldBe` int64

  describe "typeOfV" $ do
    it "EnvVar" $ do
      typeofV (EnvVar int32 "A2" ) `shouldBe` int32
    it "GVar" $ do
      typeofV ( GVar uint32 "p" ) `shouldBe` uint32
    it "TVar" $ do
      typeofV ( TVar uint32 0 ) `shouldBe` uint32
    it "SVar" $ do
      typeofV ( SVar int32 0 ) `shouldBe` int32
    it "Deref" $ do
      typeofV ( Deref $ Const (PTR int32) 0x2000 ) `shouldBe` int32
    it "foo.bar" $ do
      typeofV ( Member int32 (TVar uint32 0 ) 12 ) `shouldBe` int32
    it "foo->bar" $ do
      typeofV ( PMember int8 ( Const (PTR int32) 0x2000 ) 12 ) `shouldBe` int8
    it "foo._n[BF]" $ do
      typeofV ( BitField int16 (TVar uint32 0) 1 1 ) `shouldBe` int16
    it "foo._{n}[BF]" $ do
      typeofV ( BitFieldX int16 (TVar uint32 0)
                (Const int32 0) (Const int32 0) ) `shouldBe` int16
    it "foo[bar]" $ do
      typeofV ( Index int16 (Const (PTR VOID) 0x2000 ) (Const int16 0) ) `shouldBe` int16
  describe "cast" $ do
    let oldV = VarValue $ EnvVar uint32 "foo"
    it "cast to same type(nop)" $ do
      cast uint32 oldV `shouldBe` oldV
    it "cast to another type" $ do
      cast uint16 oldV `shouldBe` Cast uint16 oldV
    it "cast const" $ do
      cast int16 ( Const int32 22) `shouldBe` Const int16 22
    it "cast to bool" $ do
      cast BOOL oldV `shouldBe` Op2 oldV "!=" (Const uint32 0)
    it "cast to BCD" $ do
      cast BCD oldV `shouldBe` Op1 "toBCD" oldV
    it "cast to PTR" $ do
      cast (PTR VOID) oldV `shouldBe` Cast (PTR VOID) (Cast int32 oldV)
    it "cast PTR to PTR" $ do
      let oldv = VarValue $ EnvVar (PTR int8) "foo"
      cast (PTR VOID) oldv `shouldBe` Cast (PTR VOID) oldv
    it "expr2->val" $ do
      cast uint16 (Expr2 (Const uint8 2) (Const uint8 3)) `shouldBe`
        Const uint16 0x203
      cast uint32 (Expr2 (Const uint16 2) (Const uint16 3)) `shouldBe`
        Const uint32 0x20003
  describe "!" $ do
    let a = VarValue $ EnvVar BOOL "a"
    let b = VarValue $ EnvVar BOOL "b"
    it "false -> true" $ do
      lNot (Const BOOL 0) `shouldBe` Const BOOL 1
    it "true -> false" $ do
      lNot (Const BOOL 1) `shouldBe` Const BOOL 0
    it "!!a -> a" $ do
      lNot (lNot a) `shouldBe` a
    it "!(a&&b) -> (!a)||(!b)" $ do
      lNot (a $&& b) `shouldBe` (lNot a $|| lNot b)
    it "!(a||b) -> (!a)&&(!b)" $ do
      lNot (a $|| b) `shouldBe` (lNot a $&& lNot b)
    it "!(a<=b) -> a>b" $ do
      lNot (a $<= b) `shouldBe` a $> b
    it "!(a<b) -> a>=b" $ do
      lNot (a $< b) `shouldBe` a $>= b
    it "!(a>=b) -> a<b" $ do
      lNot (a $>= b) `shouldBe` a $< b
    it "!(a>b) -> a<=b" $ do
      lNot (a $> b) `shouldBe` a $<= b
    it "!(a==b) -> a!=b" $ do
      lNot (a $== b) `shouldBe` a $!= b
    it "!(a!=b) -> a==b" $ do
      lNot (a $!= b) `shouldBe` a $== b
    it "other" $ do
      lNot a `shouldBe` Op1 "!" a
