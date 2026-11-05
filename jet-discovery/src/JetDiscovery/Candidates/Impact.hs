{-# LANGUAGE DataKinds,GADTs,KindSignatures,RankNTypes,ScopedTypeVariables,TypeFamilies,UndecidableInstances #-}
-- | Single-candidate counterfactuals. Reconstruct from the shared overlay DAG,
-- expand every other candidate, then rerun full program type inference.
-- Fixed per-jet deltas are insufficient when a removed jet frees type widths.
module JetDiscovery.Candidates.Impact (isolatedCosts,directIsolatedCost) where
import Data.Proxy (Proxy(..))
import Data.Sequence (Seq)
import qualified Data.Map.Lazy as M
import qualified Data.Set as S
import GHC.TypeLits (Symbol,KnownSymbol,SomeSymbol(..),someSymbolVal,symbolVal)
import qualified Simplicity.Bitcoin.Dag as D
import qualified Simplicity.Bitcoin.JetType as J
import qualified Simplicity.Bitcoin.Jets as B
import qualified Simplicity.Bitcoin.Inference as I
import Simplicity.Ty (Ty,TyC,UntypedValue,someArrowMap,SomeArrow)
import Simplicity.Weight (milliWeight)
import JetDiscovery.Cost (TermWeight,milliWeigh)
import JetDiscovery.JetSets (Candidate(..),SomeCandidate(..))
import JetDiscovery.Candidates.Registry (candidates,candidateInfo,ciName)
import JetDiscovery.WhatIf (WhatIf(..))
import JetDiscovery.Profile (profile,niTotal,niKind,niMult)
import JetDiscovery.Types (Prog(..))
import qualified Simplicity.Bitcoin.Term as Term

newtype Only (name :: Symbol) a b=Only (WhatIf a b)
instance KnownSymbol name => J.JetType (Only name) where
  type MatcherInfo (Only name)=J.MatcherInfo WhatIf
  specification (Only j)=J.specification j
  implementation (Only j)=J.implementation j
  matcher m=do
    j<-J.matcher m
    case j of
      Known _->Just (Only j)
      Cand c | candName c==symbolVal (Proxy :: Proxy name)->Just (Only j)
             | otherwise->Nothing
  getJetBit abort next=someArrowMap Only <$> J.getJetBit abort next
  putJetBit (Only j)=J.putJetBit j
  jetCost (Only j)=J.jetCost j

newtype Except (name :: Symbol) a b=Except (WhatIf a b)
instance KnownSymbol name => J.JetType (Except name) where
  type MatcherInfo (Except name)=J.MatcherInfo WhatIf
  specification (Except j)=J.specification j
  implementation (Except j)=J.implementation j
  matcher m=do
    j<-J.matcher m
    case j of
      Known _->Just (Except j)
      Cand c | candName c/=symbolVal (Proxy :: Proxy name)->Just (Except j)
             | otherwise->Nothing
  getJetBit abort next=someArrowMap Except <$> J.getJetBit abort next
  putJetBit (Except j)=J.putJetBit j
  jetCost (Except j)=J.jetCost j

label :: (TyC a,TyC b) => WhatIf a b -> String
label (Known _)="known"
label (Cand c)="cand:"++candName c

-- Exclude a candidate's own root and inspect every branch for other candidate
-- nodes. Transitive closure gives a conservative affected set, including
-- candidates hidden by a larger candidate in the combined overlay.
dependenciesOf :: SomeCandidate -> [String]
dependenciesOf sc@(SomeCandidate c)=case someSymbolVal (candName c) of SomeSymbol p->forName p sc
 where
  forName :: forall name. KnownSymbol name => Proxy name -> SomeCandidate -> [String]
  forName _ (SomeCandidate (c :: Candidate a b))=case c of
    Candidate _ _ spec->
      let prof=profile (\(Except j)->label j) (\j->milliWeight (J.jetCost j)) (const Nothing) (D.jetDag (spec :: D.JetDag (Except name) a b))
      in S.toList (S.fromList [drop 9 (niKind n)|n<-prof,take 9 (niKind n)=="jet:cand:"])
{-# NOINLINE dependencies #-}
dependencies :: M.Map String [String]
dependencies=M.fromList [(candName c,dependenciesOf sc)|sc@(SomeCandidate c)<-candidates]
closure :: [String] -> S.Set String
closure=go S.empty
 where
  go seen []=seen
  go seen (x:xs) | S.member x seen=go seen xs
                 | otherwise=go (S.insert x seen) (M.findWithDefault [] x dependencies++xs)

type OverlayDag=I.SimplicityDag Seq Ty (SomeArrow WhatIf) UntypedValue
-- Each row records the static bound, selected-path multiplicity, and
-- distinct matched DAG nodes including off-path branches.
isolatedCosts :: Integer -> [String] -> OverlayDag -> [(String,(Integer,Integer,Integer))]
isolatedCosts nativeCost direct dag=[(name,if S.member name affected then scenario name else (nativeCost,0,0))|name<-map ciName candidateInfo]
 where
  affected=closure direct
  scenario name=case someSymbolVal name of SomeSymbol p->forName p
  forName :: forall name. KnownSymbol name => Proxy name -> (Integer,Integer,Integer)
  forName _=
    let raw=either (error.("candidate reconstruction: "++)) id (I.typeCheck dag) :: D.JetDag (Only name) () ()
        prof=profile (\(Only j)->label j) (\j->milliWeight (J.jetCost j)) (const Nothing) (D.jetDag raw)
        matches=[n|n<-prof,niKind n=="jet:cand:"++symbolVal (Proxy :: Proxy name)]
    in (niTotal (last prof),sum (map niMult matches),toInteger (length matches))

-- Independent whole-program route for regression tests, without starting
-- from any combined overlay or using the dependency shortcut.
directIsolatedCost :: String -> Prog -> Integer
directIsolatedCost name program=directTerm name (unProg program)

directTerm :: String -> (forall term. (Term.Simplicity term,Term.Primitive term) => term () ()) -> Integer
directTerm name p=case someSymbolVal name of SomeSymbol proxy->forName proxy
 where
  forName :: forall name. KnownSymbol name => Proxy name -> Integer
  forName _=milliWeigh (B.unwrap (D.jetSubst (p :: D.JetDag (Only name) () ())) :: TermWeight () ())
