module Ircert where
import Data.List
import Test.SmallCheck

{- Types -}

type User = Int
type Channel = Int

data Command =
   Join User Channel
 | Part User Channel
 | Privmsg User Channel String

data Response =
   Evn_Join User User Channel
 | Evn_Part User User Channel
  deriving Eq

type Users = [User]
type Responses = [Response]
type State = [(Channel , Users)]

{- Predicates -}

inUsers :: User -> Users -> Bool
inUsers = elem

members :: Channel -> State -> Users
members _ [] = []
members chn ((chn' , usrs) : xs) = if chn == chn'
  then usrs
  else members chn xs

inChannel :: User -> Channel -> State -> Bool
inChannel usr chn xs = inUsers usr (members chn xs)

emptyChannel :: Channel -> State -> Bool
emptyChannel chn xs = members chn xs == []

inResponses :: Response -> Responses -> Bool
inResponses = elem

{- Commands -}

joinChannel :: User -> Channel -> State -> Responses
joinChannel usr chn xs = map (\x -> Evn_Join x usr chn) (usr : members chn xs)

joinChannel' :: User -> Channel -> State -> State
joinChannel' usr chn [] = [(chn , [usr])]
joinChannel' usr chn ((chn' , usrs) : xs) = if chn == chn'
  then (chn' , usr : usrs) : xs
  else (chn' , usrs) : joinChannel' usr chn xs

partChannel :: User -> Channel -> State -> Responses
partChannel usr chn xs = map (\x -> Evn_Part x usr chn) (usr : members chn xs)

partChannel' :: User -> Channel -> State -> State
partChannel' _ _ [] = []
partChannel' usr chn ((chn' , usrs) : xs)
  | chn == chn' && usrs == [usr] = xs
  | chn == chn' = (chn' , delete usr usrs) : xs
  | otherwise = (chn' , usrs) : partChannel' usr chn xs

respond :: Command -> State -> (Responses , State)
respond (Join usr chn) xs = (joinChannel usr chn xs , joinChannel' usr chn xs)
respond (Part _ _) _ = undefined
respond (Privmsg _ _ _) _ = undefined

{- Properties -}

prop_joiner_gets_message :: User -> Channel -> State -> Bool
prop_joiner_gets_message usr chn xs =
  inResponses (Evn_Join usr usr chn) (joinChannel usr chn xs)

prop_join_implies_in_channel :: User -> Channel -> State -> Bool
prop_join_implies_in_channel usr chn xs =
  inChannel usr chn (joinChannel' usr chn xs)

prop_all_members_get_join_message :: User -> User -> Channel -> State -> Property
prop_all_members_get_join_message usr joiner chn xs =
  let xs' = joinChannel' usr chn xs in
  inChannel usr chn xs' ==>
  inResponses (Evn_Join usr joiner chn) (joinChannel joiner chn xs')

prop_parter_gets_message :: User -> Channel -> State -> Bool
prop_parter_gets_message usr chn xs =
  inResponses (Evn_Part usr usr chn) (partChannel usr chn xs)

prop_part_implies_not_in_channel :: User -> Channel -> State -> Bool
prop_part_implies_not_in_channel usr chn xs =
  let xs' = map (\x -> (fst x , nub (snd x))) xs in
  -- no duplicate users ==>
  -- no duplicate channels ==>
  not $ inChannel usr chn (partChannel' usr chn xs')

prop_all_members_get_part_message :: User -> User -> Channel -> State -> Property
prop_all_members_get_part_message usr parter chn xs =
  let xs' = joinChannel' usr chn xs in
  inChannel usr chn xs' ==>
  inResponses (Evn_Part usr parter chn) (partChannel parter chn xs')

prop_part_left_inverse_of_join :: User -> Channel -> State -> Property
prop_part_left_inverse_of_join usr chn xs =
  not (emptyChannel chn xs) ==>
  not (inChannel usr chn xs) ==>
  partChannel' usr chn (joinChannel' usr chn xs) == xs

main :: IO ()
main = let n = 3 in do
  putStrLn "Any user that joines a channel gets a message about it:"
  smallCheck n prop_joiner_gets_message
  putStrLn "Joining a channel satisfies the inChannel predicate:"
  smallCheck n prop_join_implies_in_channel
  putStrLn "Any user in a channel gets a message about a join:"
  smallCheck n prop_all_members_get_join_message
  putStrLn "Any user that parts a channel gets a message about it:"
  smallCheck n prop_parter_gets_message
  putStrLn "Parting a channel dissatisfies the inChannel predicate:"
  smallCheck n prop_part_implies_not_in_channel
  putStrLn "Any user in a channel gets a message about a part:"
  smallCheck n prop_all_members_get_part_message
  putStrLn "Part is the left inverse of join:"
  smallCheck n prop_part_left_inverse_of_join
  putStrLn "Done!"
