import Convert
import Data
import Interp
import TypeCheck

main :: IO ()
main = do {
  -- test for terms
  let t0 = TmUnit
  ; print (interp [] (PgTm t0))

  ; let t1 =  (TmInt 32)
  ; print (interp [] (PgTm t1))

  ; let t3 = TmVar "x"
  ; let e3 = (PgTm t3)
  ; let env3 = [("x" , PB PBValUnit) , ("y" , PB $ PBValInt 32)]
  ; print (interp env3 e3)

  ; let env4 = [("x" , PB $ PBValInt 4) , ("y" , PB $ PBValInt 32) , ("x" , PB PBValUnit)]
  ; print (interp env4 e3)

  ; let env5 = [("y" , PB $ PBValInt 32)]
  ; print (interp env5 e3)

  ; let t4 = (TmLInj t3)
  ; print (interp env5 (PgTm t4))

  ; let t5 = (TmRInj t1)
  ; print (interp env5 (PgTm t5))

  ; let t6 = TmPair t4 t5
  ; print (interp env3 (PgTm t6))

  ; let t7 = TmLet (PtMultiVar ["x", "y"]) t6 (TmLInj (TmVar "x"))
  ; print (interp env3 (PgTm t7))

  ; let t8 = TmLet (PtMultiVar ["x", "y", "z"]) t6 (TmLInj (TmVar "x"))
  ; print (interp env3 (PgTm t8))

  ; let t9 = TmLet (PtSingleVar "x") t6 (TmVar "x")
  ; print (interp env3 (PgTm t9))

  -- test for terms
  ; let tlv = (BTySum BTyUnit (BTySum BTyUnit (BTySum BTyUnit BTyUnit)))
  ; let v0 = ValLInj ValUnit
  ; let v1 = ValRInj (ValLInj ValUnit)
  ; let v2 = ValRInj (ValRInj (ValLInj ValUnit))
  ; let v3 = ValRInj (ValRInj (ValRInj ValUnit))
  ; let lhs = [v0, v1, v2, v3]
  ; let i0 = IsoValue $ zip lhs (map ExpVal (reverse lhs))
  ; print (interp env3 (PgIs i0))

  ; let i1 = TmIsoApp i0 (TmLInj t0)
  ; print (interp [] (PgTm i1))

  ; let vlPat = ValAnn (ValLInj (ValVar "vl")) tlv
  ; let vrPat = ValAnn (ValRInj (ValVar "vr")) tlv
  ; let lhsPat = [vlPat, vrPat]
  ; let trv = (BTySum (BTySum BTyUnit (BTySum BTyUnit BTyUnit)) BTyUnit)
  ; let elPat = ValAnn (ValRInj (ValVar "vl")) trv
  ; let erPat = ValAnn (ValLInj (ValVar "vr")) trv
  ; let rhsPat = [ExpVal elPat, ExpVal erPat]
  ; let i2 = IsoValue $ zip lhsPat rhsPat
  ; let i3 = TmIsoApp i2 (TmRInj (TmRInj (TmLInj t0)))
  ; print (interp [] (PgTm i3))
  ; print (typeInfer [] (PgTm i3))

  -- ; let e20 = PgIs $ IsoValue [ValUnit] [ExpVal (ValPair ValUnit ValUnit)]
  -- ; print (interp [] e20)
  -- ; let m1 = matrixize [("a" , 0 :: Int) , ("b" , 2 :: Int), ("c" , 3 :: Int)]
  -- ; print m1
  }
