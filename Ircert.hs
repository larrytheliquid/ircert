module Ircert where
import Data.List
import Test.SmallCheck

{- Types -}

type User = Int
type Channel = Int

data Command =
   Join User Channel
 | Part User Channel

data Response =
   Evn_Join User User Channel
 | Evn_Part User User Channel
  deriving Eq

type Commands = [Command]
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
respond (Part usr chn) xs = (partChannel usr chn xs , partChannel' usr chn xs)

serve' :: Commands -> (Responses , State) -> (Responses , State)
serve' [] x = x
serve' (c : cs) (rs , xs) =
  let (rs' , xs') = respond c xs in
  serve' cs (rs ++ rs' , xs')

serve :: Commands -> (Responses , State)
serve cs = serve' cs ([] , [])

serveR :: Commands -> Responses
serveR = fst . serve

serveS :: Commands -> State
serveS = snd . serve

{- Properties -}

prop_joiner_gets_message :: User -> Channel -> Bool
prop_joiner_gets_message usr chn =
  inResponses (Evn_Join usr usr chn) $ serveR [Join usr chn]

prop_join_implies_in_channel :: User -> Channel -> Bool
prop_join_implies_in_channel usr chn =
  inChannel usr chn $ serveS [Join usr chn]

prop_all_members_get_join_message :: User -> User -> Channel -> Bool
prop_all_members_get_join_message usr joiner chn =
  inResponses (Evn_Join usr joiner chn) $ serveR [Join usr chn, Join joiner chn]

prop_parter_gets_message :: User -> Channel -> Bool
prop_parter_gets_message usr chn =
  inResponses (Evn_Part usr usr chn) $ serveR [Part usr chn]

prop_part_implies_not_in_channel :: User -> Channel -> Bool
prop_part_implies_not_in_channel usr chn =
  not $ inChannel usr chn $ serveS [Part usr chn]

prop_all_members_get_part_message :: User -> User -> Channel -> Bool
prop_all_members_get_part_message usr parter chn =
  inResponses (Evn_Part usr parter chn) $ serveR [Join usr chn, Part parter chn]

prop_part_left_inverse_of_join :: User -> Channel -> Bool
prop_part_left_inverse_of_join usr chn =
  let before = serve [] in
  snd (serve' [Join usr chn, Part usr chn] before) == snd before

header :: String -> IO ()
header x = putStrLn $ "\n[" ++ x ++ "]"

main :: IO ()
main = let n = 3 in do
  header "Any user that joines a channel gets a message about it"
  smallCheck n prop_joiner_gets_message
  header "Joining a channel satisfies the inChannel predicate"
  smallCheck n prop_join_implies_in_channel
  header "Any user in a channel gets a message about a join"
  smallCheck n prop_all_members_get_join_message
  header "Any user that parts a channel gets a message about it"
  smallCheck n prop_parter_gets_message
  header "Parting a channel dissatisfies the inChannel predicate"
  smallCheck n prop_part_implies_not_in_channel
  header "Any user in a channel gets a message about a part"
  smallCheck n prop_all_members_get_part_message
  header "Part is the left inverse of join"
  smallCheck n prop_part_left_inverse_of_join
  putStrLn "... Done!"
