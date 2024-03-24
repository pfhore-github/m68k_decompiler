module UtilSpec(testUtil) where

import Util
import Test.Hspec
import Test.QuickCheck
import Test.Hspec.QuickCheck

testUtil :: SpecWith ()
testUtil = describe "util" $ do
  testBetween
  testBetweenX
  testSplitBlock
  testToS8
  testToS16
  testToS32
  testGetBit
  
testBetween :: SpecWith ()
testBetween = describe "between" $ do
  let genInt = arbitrary :: Gen Int
  prop "under" $
    forAll genInt $ \l -> 
    forAll (suchThat genInt (> l)) $ \h -> 
    forAll (suchThat genInt (< l)) $ \v -> 
        between l h v `shouldBe` False 
  prop "low" $
    forAll genInt $ \l -> 
    forAll (suchThat genInt (> l)) $ \h -> 
        between l h l `shouldBe` True
  prop "in" $
    forAll genInt $ \l -> 
    forAll (suchThat genInt (> l)) $ \v -> 
    forAll (suchThat genInt (> v)) $ \h -> 
        between l h v `shouldBe` True
  prop "high" $
    forAll genInt $ \l -> 
    forAll (suchThat genInt (> l)) $ \h -> 
        between l h h `shouldBe` True
  prop "over" $
    forAll genInt $ \l -> 
    forAll (suchThat genInt (> l)) $ \h -> 
    forAll (suchThat genInt (> h)) $ \v -> 
        between l h v `shouldBe` False 

testBetweenX :: SpecWith ()
testBetweenX = describe "between" $ do
  let genInt = arbitrary :: Gen Int
  prop "under" $
    forAll genInt $ \l -> 
    forAll (suchThat genInt (> l)) $ \h -> 
    forAll (suchThat genInt (< l)) $ \v -> 
        betweenX l h v `shouldBe` False 
  prop "low" $
    forAll genInt $ \l -> 
    forAll (suchThat genInt (> l)) $ \h -> 
        betweenX l h l `shouldBe` False
  prop "in" $
    forAll genInt $ \l -> 
    forAll (suchThat genInt (> l)) $ \v -> 
    forAll (suchThat genInt (> v)) $ \h -> 
        betweenX l h v `shouldBe` True
  prop "high" $
    forAll genInt $ \l -> 
    forAll (suchThat genInt (> l)) $ \h -> 
        betweenX l h h `shouldBe` False
  prop "over" $
    forAll genInt $ \l -> 
    forAll (suchThat genInt (> l)) $ \h -> 
    forAll (suchThat genInt (> h)) $ \v -> 
        betweenX l h v `shouldBe` False 

testSplitBlock :: SpecWith ()
testSplitBlock = describe "splitBlock" $ do
  it "cont" $ do
    let c = [1,2,3] :: [Int]
    splitBlock (const SplitCont) c `shouldBe` [c]
  it "before" $ do
    let c = [1,2,0,3] :: [Int]
    splitBlock (\x -> if x == 0 then SplitBefore else SplitCont) c `shouldBe`
      [[1,2],[0,3]]
  it "both" $ do
    let c = [1,2,0,3] :: [Int]
    splitBlock (\x -> if x == 0 then SplitBoth else SplitCont) c `shouldBe`
      [[1,2],[0],[3]]

testToS8 :: SpecWith ()
testToS8 = describe "toS8" $ do
  prop "positive" $
    forAll (chooseInt(1, 127)) $ \v -> toS8 v `shouldBe` v
  it "zero" $ do
    toS8 0 `shouldBe` 0
  prop "negative" $
    forAll (chooseInt(128, 255)) $ \v -> (v - toS8 v) `shouldBe` 256

testToS16 :: SpecWith ()
testToS16 = describe "toS16" $ do
  prop "positive" $
    forAll (chooseInt(1, 0x7FFF)) $ \v -> toS16 v `shouldBe` v
  it "zero" $ do
    toS16 0 `shouldBe` 0
  prop "negative" $
    forAll (chooseInt(0x8000, 0xFFFF)) $
    \v -> (v - toS16 v) `shouldBe` 0x10000

testToS32 :: SpecWith ()
testToS32 = describe "toS32" $ do
  prop "positive" $
    forAll (chooseInt(1, 0x7FFFFFFF)) $ \v -> toS32 v `shouldBe` v
  it "zero" $ do
    toS32 0 `shouldBe` 0
  prop "negative" $
    forAll (chooseInt(0x80000000, 0xFFFFFFFF)) $ \v ->
    (v - toS32 v) `shouldBe` 0x100000000

testGetBit :: SpecWith ()
testGetBit = describe "getBit" $ do
  it "pos=0" $ do
    getBit 0xff 0 0xf `shouldBe` 0xf
  it "pos>0" $ do
    getBit 0xf0 4 0xf `shouldBe` 0xf

