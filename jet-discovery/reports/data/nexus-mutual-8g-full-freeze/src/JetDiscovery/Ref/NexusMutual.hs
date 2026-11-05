-- | Independent Integer model of the funded native cover and claim ledger.
module JetDiscovery.Ref.NexusMutual
  ( Owner(..), Role(..), Slot(..), Verdict(..), Phase(..), Policy(..), State(..)
  , Action(..), Step(..), anchor, deposit, fee, maxCapital, maxCover, maxClaimId
  , setup, exposure, refundable, value, premium, transition, encode, referenceAudit
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as C
import Data.Serialize (putWord8, putWord16be, putWord32be, runPut)

data Owner = Alice | Bob deriving (Eq,Show,Enum)
data Role = CapitalProvider | Assessor | PolicyOwner Owner deriving (Eq,Show)
data Slot = First | Second deriving (Eq,Show,Enum)
data Verdict = AcceptClaim | DenyClaim | DrawClaim deriving (Eq,Show,Enum)
data Phase = Unused | Available | Pending | Accepted | Draw | Denied
           | Paid | DepositReturned | Surrendered deriving (Eq,Show,Enum)
data Policy = Policy
  { phase :: Phase
  , owner :: Owner
  , claimId :: Integer
  , cover :: Integer
  , requested :: Integer
  } deriving (Eq,Show)
data State = State
  { capital :: Integer
  , policies :: (Policy,Policy)
  } deriving (Eq,Show)
data Action = Fund Integer | Withdraw Integer | ClosePool | Buy Slot Owner Integer
            | Transfer Slot | Submit Slot Integer | Assess Slot Verdict
            | Redeem Slot | ReturnDraw Slot | Surrender Slot deriving (Eq,Show)
data Step = Step
  { nextState :: Maybe State
  , authorization :: Maybe Role
  , funding :: Maybe (Role,Integer)
  , payout :: Maybe (Role,Integer)
  } deriving (Eq,Show)

anchor, deposit, fee, maxCapital, maxCover, maxClaimId :: Integer
anchor = 1000
deposit = 1000
fee = 3000
maxCapital = 10000000
maxCover = 4000000
maxClaimId = 65535

unused :: Policy
unused = Policy Unused Alice 0 0 0

setup :: State
setup = State 0 (unused,unused)

hasDeposit :: Policy -> Bool
hasDeposit p = phase p `elem` [Pending,Accepted,Draw]

claimable :: Policy -> Bool
claimable p = cover p > 0 && phase p `elem` [Available,Denied,Paid,DepositReturned]

exposure :: State -> Integer
exposure (State _ (first,second)) = cover first + cover second

refundable :: State -> Integer
refundable (State _ (first,second)) = deposit * toInteger (length (filter hasDeposit [first,second]))

value :: State -> Integer
value s = anchor + capital s + refundable s

premium :: Integer -> Integer
premium amount = (amount + 9) `div` 10

valid :: State -> Bool
valid s@(State c (first,second)) = exposure s <= c && c + refundable s <= maxCapital &&
  all validPolicy [first,second]
 where
  validPolicy p = between 0 maxClaimId (claimId p) && between 0 maxCover (cover p) &&
    case phase p of
      Unused -> p == unused
      Available -> cover p > 0 && claimId p == 0 && requested p == 0
      Pending -> openClaim p
      Accepted -> openClaim p
      Draw -> openClaim p
      Denied -> settled p && cover p > 0
      Paid -> settled p
      DepositReturned -> settled p && cover p > 0
      Surrendered -> cover p == 0 && requested p == 0
  openClaim p = claimId p > 0 && between 1 (cover p) (requested p)
  settled p = claimId p > 0 && requested p == 0
  between low high x = low <= x && x <= high

transition :: State -> Action -> Maybe Step
transition old@(State reserve (first,second)) action
  | not (valid old) = Nothing
  | otherwise = case action of
      Fund amount | amount > 0 ->
        keep (old { capital = reserve + amount }) (Just CapitalProvider)
          (Just (CapitalProvider,amount)) Nothing
      Withdraw amount | amount > 0 && amount <= reserve - exposure old ->
        keep (old { capital = reserve - amount }) (Just CapitalProvider)
          Nothing (Just (CapitalProvider,amount))
      ClosePool | exposure old == 0 && refundable old == 0 ->
        Just (Step Nothing (Just CapitalProvider) Nothing (Just (CapitalProvider,value old)))
      Buy slot who amount | phase (at slot) == Unused && amount > 0 && amount <= maxCover ->
        let debit = premium amount
            next = update slot (Policy Available who 0 amount 0)
            holder = PolicyOwner who
        in keep (next { capital = reserve + debit }) (Just holder) (Just (holder,debit)) Nothing
      Transfer slot | cover (at slot) > 0 ->
        let p = at slot
            nextOwner = if owner p == Alice then Bob else Alice
        in updateOnly slot (p { owner = nextOwner }) (Just (PolicyOwner (owner p)))
      Submit slot amount | claimable (at slot) && amount > 0 && amount <= cover (at slot)
                            && claimId (at slot) < maxClaimId ->
        let p = at slot
            holder = PolicyOwner (owner p)
            next = update slot (p { phase = Pending, claimId = claimId p + 1, requested = amount })
        in keep next (Just holder) (Just (holder,deposit)) Nothing
      Assess slot verdict | phase (at slot) == Pending ->
        let p = at slot
        in case verdict of
          AcceptClaim -> updateOnly slot (p { phase = Accepted }) (Just Assessor)
          DrawClaim -> updateOnly slot (p { phase = Draw }) (Just Assessor)
          DenyClaim ->
            let next = update slot (p { phase = Denied, requested = 0 })
            in keep (next { capital = reserve + deposit }) (Just Assessor) Nothing Nothing
      Redeem slot | phase (at slot) == Accepted ->
        let p = at slot
            amount = requested p
            holder = PolicyOwner (owner p)
            next = update slot (p { phase = Paid, cover = cover p - amount, requested = 0 })
        in keep (next { capital = reserve - amount }) (Just holder) Nothing (Just (holder,amount + deposit))
      ReturnDraw slot | phase (at slot) == Draw ->
        let p = at slot
            next = update slot (p { phase = DepositReturned, requested = 0 })
        in keep next Nothing Nothing (Just (PolicyOwner (owner p),deposit))
      Surrender slot | claimable (at slot) ->
        let p = at slot
        in updateOnly slot (p { phase = Surrendered, cover = 0 }) (Just (PolicyOwner (owner p)))
      _ -> Nothing
 where
  at First = first
  at Second = second
  update First p = old { policies = (p,second) }
  update Second p = old { policies = (first,p) }
  updateOnly slot p signer = keep (update slot p) signer Nothing Nothing
  keep s signer funded paid
    | valid s && value old + amount funded == value s + amount paid =
        Just (Step (Just s) signer funded paid)
    | otherwise = Nothing
  amount = maybe 0 snd

encode :: State -> BS.ByteString
encode (State reserve (first,second)) = C.pack "NMX1" <> runPut (do
  putWord32be (fromInteger reserve)
  putPolicy first
  putPolicy second)
 where
  putPolicy p = do
    putWord8 (fromIntegral (fromEnum (phase p)))
    putWord8 (fromIntegral (fromEnum (owner p)))
    putWord16be (fromInteger (claimId p))
    putWord32be (fromInteger (cover p))
    putWord32be (fromInteger (requested p))

referenceAudit :: Bool
referenceAudit = and
  [ value setup == anchor
  , BS.length (encode setup) == 32
  , premium 10001 == 1001
  , exposure issued == 80000 && capital issued == 88000
  , refundable pendingBoth == 2*deposit && value pendingBoth == 91000
  , transition pendingBoth (Withdraw 8001) == Nothing
  , funding (step issued (Submit First 20000)) == Just (PolicyOwner Alice,deposit)
  , transition pendingBoth (Submit First 10000) == Nothing
  , payout (step transferred (Redeem First)) == Just (PolicyOwner Bob,21000)
  , exposure paid == 60000 && capital paid == 68000 && refundable paid == deposit
  , transition paid (Redeem First) == Nothing
  , payout (step draw (ReturnDraw Second)) == Just (PolicyOwner Bob,deposit)
  , authorization (step draw (ReturnDraw Second)) == Nothing
  , capital afterDraw == capital paid && exposure afterDraw == exposure paid && refundable afterDraw == 0
  , transition afterDraw (ReturnDraw Second) == Nothing
  , capital denied == 89000 && refundable denied == deposit && exposure denied == exposure issued
  , transition denied (Redeem First) == Nothing && transition denied (ReturnDraw First) == Nothing
  , claimId (fst (policies (advance denied (Submit First 10000)))) == 2
  , transition pendingBoth (Surrender First) == Nothing
  , payout (step surrendered ClosePool) == Just (CapitalProvider,value surrendered)
  ]
 where
  step s a = maybe (error ("bad Nexus reference audit action " ++ show a)) id (transition s a)
  advance s a = maybe (error "Nexus reference audit reached terminal state") id (nextState (step s a))
  issued = foldl advance setup [Fund 80000,Buy First Alice 50000,Buy Second Bob 30000]
  pendingBoth = foldl advance issued [Submit First 20000,Submit Second 10000]
  transferred = foldl advance pendingBoth [Assess First AcceptClaim,Transfer First]
  paid = advance transferred (Redeem First)
  draw = advance paid (Assess Second DrawClaim)
  afterDraw = advance draw (ReturnDraw Second)
  denied = advance pendingBoth (Assess First DenyClaim)
  surrendered = foldl advance afterDraw [Surrender First,Surrender Second]
