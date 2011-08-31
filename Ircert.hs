module Ircert where
import Data.List
import Test.SmallCheck

{- Types -}

type User = Int
type Channel = String

data Command =
   Join User (Maybe Channel)
 | Part User (Maybe Channel)
 | Privmsg User (Maybe Channel) (Maybe String)
 | Unknown User String
 deriving (Eq, Show)

instance Serial Command where
  series =
       cons2 Join
    \/ cons2 Part
    \/ cons3 Privmsg
    \/ cons2 Unknown

data Response =
   Evn_Join User User Channel
 | Evn_Part User User Channel
 | Evn_Privmsg User User Channel String

 -- Err 400-599
 | Err_Nosuchnick User Channel -- 401
 | Err_Cannotsendtochan User Channel -- 404
 | Err_Norecipient User String -- 411
 | Err_Notexttosend User -- 412
 | Err_Unknowncommand User String -- 421
 | Err_Notonchannel User Channel -- 442
 | Err_Needmoreparams User Channel -- 461
  deriving (Eq, Show)

type Context = (Responses , State)
type Commands = [Command]
type Responses = [Response]
type State = [(Channel , Users)]
type Users = [User]

{- Predicates -}

inUsers :: User -> Users -> Bool
inUsers = elem

members :: Channel -> State -> Users
members _ [] = []
members chn ((chn' , usrs) : xs) = if chn == chn'
  then usrs
  else members chn xs

channelExists :: Channel -> State -> Bool
channelExists chn xs = elem chn (map fst xs)

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
joinChannel' usr chn ((chn' , usrs) : xs) 
  | chn == chn' && inUsers usr usrs = (chn' , usrs) : xs
  | chn == chn' = (chn' , usr : usrs) : xs
  | otherwise = (chn' , usrs) : joinChannel' usr chn xs

partChannel :: User -> Channel -> State -> Responses
partChannel usr chn [] = [Err_Notonchannel usr chn]
partChannel usr chn ((chn' , usrs) : xs) = if chn == chn'
  then map (\x -> Evn_Part x usr chn) (usr : usrs)
  else partChannel usr chn xs

partChannel' :: User -> Channel -> State -> State
partChannel' _ _ [] = []
partChannel' usr chn ((chn' , usrs) : xs)
  | chn == chn' && usrs == [usr] = xs
  | chn == chn' = (chn' , delete usr usrs) : xs
  | otherwise = (chn' , usrs) : partChannel' usr chn xs

msgChannel :: User -> Channel -> String -> State -> Responses
msgChannel usr chn msg xs 
  | not (channelExists chn xs) = [Err_Nosuchnick usr chn]
  | not (inChannel usr chn xs) = [Err_Cannotsendtochan usr chn]
  | otherwise = map (\x -> Evn_Privmsg x usr chn msg) (members chn xs)

respond :: Command -> State -> Context
respond (Join usr (Just chn)) xs = (joinChannel usr chn xs , joinChannel' usr chn xs)
respond (Join usr Nothing) xs = ([Err_Needmoreparams usr "Join"] , xs)
respond (Part usr (Just chn)) xs = (partChannel usr chn xs , partChannel' usr chn xs)
respond (Part usr Nothing) xs = ([Err_Needmoreparams usr "Part"] , xs)
respond (Privmsg usr (Just chn) (Just msg)) xs = (msgChannel usr chn msg xs , xs)
respond (Privmsg usr (Just _) Nothing) xs = ([Err_Notexttosend usr] , xs)
respond (Privmsg usr Nothing _) xs = ([Err_Norecipient usr "Privmsg"] , xs)
respond (Unknown usr cmd) xs = ([Err_Unknowncommand usr cmd] , xs)

serve' :: Context -> Commands -> Context
serve' ctx [] = ctx
serve' (rs , xs) (c : cs) =
  let (rs' , xs') = respond c xs in
  serve' (rs ++ rs' , xs') cs

serveR :: State -> Commands -> Responses
serveR xs cs = fst $ serve' ([] , xs) cs

serveS :: State -> Commands -> State
serveS xs cs = snd $ serve' ([] , xs) cs

serve :: Commands -> Context
serve cs = serve' ([] , []) cs

{- Properties -}

prop_join_implies_in_channel :: Commands -> User -> Channel -> Bool
prop_join_implies_in_channel cs usr chn =
  let xs = snd $ serve cs in
  inChannel usr chn $ serveS xs [Join usr (Just chn)]

prop_all_members_get_join_message :: Commands -> User -> User -> Channel -> Bool
prop_all_members_get_join_message cs usr joiner chn =
  let xs = snd $ serve (cs ++ [Join usr (Just chn)]) in
  inResponses (Evn_Join usr joiner chn) $ serveR xs [Join joiner (Just chn)]

prop_joiner_gets_message :: Commands -> User -> Channel -> Bool
prop_joiner_gets_message cs usr chn =
  let xs = snd $ serve cs in
  inResponses (Evn_Join usr usr chn) $ serveR xs [Join usr (Just chn)]

prop_part_implies_not_in_channel :: Commands -> User -> Channel -> Bool
prop_part_implies_not_in_channel cs usr chn =
  let xs = snd $ serve cs in
  not $ inChannel usr chn $ serveS xs [Part usr (Just chn)]

prop_all_members_get_part_message :: Commands -> User -> User -> Channel -> Bool
prop_all_members_get_part_message cs usr parter chn =
  let xs = snd $ serve (cs ++ [Join usr (Just chn)]) in
  inResponses (Evn_Part usr parter chn) $ serveR xs [Part parter (Just chn)]

prop_parter_gets_message :: Commands -> User -> Channel -> Bool
prop_parter_gets_message cs usr chn =
  let xs = snd $ serve (cs ++ [Join usr (Just chn)]) in
  inResponses (Evn_Part usr usr chn) $ serveR xs [Part usr (Just chn)]

prop_part_left_inverse_of_join :: Commands -> User -> Channel -> Bool
prop_part_left_inverse_of_join cs usr chn =
  let xs = snd $ serve (cs ++ [Part usr (Just chn)]) in
  serveS xs [Join usr (Just chn), Part usr (Just chn)] == xs

prop_all_members_get_privmsg_message :: Commands -> User -> User -> Channel -> String -> Bool
prop_all_members_get_privmsg_message cs usr sender chn msg =
  let xs = snd $ serve (cs ++ [Join usr (Just chn), Join sender (Just chn)]) in
  inResponses (Evn_Privmsg usr sender chn msg) $ serveR xs [Privmsg sender (Just chn) (Just msg)]

header :: String -> IO ()
header x = putStrLn $ "\n[" ++ x ++ "]"

main :: IO ()
main = let n = 3 in do
  header "Joining a channel satisfies the inChannel predicate"
  smallCheck n prop_join_implies_in_channel
  header "Any user in a channel gets a message about a join"
  smallCheck n prop_all_members_get_join_message
  header "Any user that joines a channel gets a message about it"
  smallCheck n prop_joiner_gets_message

  header "Parting a channel dissatisfies the inChannel predicate"
  smallCheck n prop_part_implies_not_in_channel
  header "Any user in a channel gets a message about a part"
  smallCheck n prop_all_members_get_part_message
  header "Any user that parts a channel gets a message about it"
  smallCheck n prop_parter_gets_message
  header "Part is the left inverse of join"
  smallCheck n prop_part_left_inverse_of_join

  header "Any user in a channel gets a message sent to it"
  smallCheck n prop_all_members_get_privmsg_message

  putStrLn "\nDone!"
