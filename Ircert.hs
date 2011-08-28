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
 deriving (Eq, Show)

instance Serial Command where
  series = cons2 Join \/ cons2 Part \/ cons3 Privmsg

data Response =
   Evn_Join User User Channel
 | Evn_Part User User Channel
 | Evn_Privmsg User User Channel String

 | Err_Cannotsendtochan User Channel
 | Err_Nosuchnick User Channel
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
partChannel usr chn xs = map (\x -> Evn_Part x usr chn) (usr : members chn xs)

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
respond (Join usr chn) xs = (joinChannel usr chn xs , joinChannel' usr chn xs)
respond (Part usr chn) xs = (partChannel usr chn xs , partChannel' usr chn xs)
respond (Privmsg usr chn msg) xs = (msgChannel usr chn msg xs , xs)

serve' :: Context -> Commands -> Context
serve' ctx [] = ctx
serve' (rs , xs) (c : cs) =
  let (rs' , xs') = respond c xs in
  serve' (rs ++ rs' , xs') cs

serveR :: Context -> Commands -> Responses
serveR ctx cs = fst $ serve' ctx cs

serveS :: Context -> Commands -> State
serveS ctx cs = snd $ serve' ctx cs

serve :: Commands -> Context
serve cs = serve' ([] , []) cs

{- Properties -}

prop_join_implies_in_channel :: Commands -> User -> Channel -> Bool
prop_join_implies_in_channel cs usr chn =
  let ctx = serve cs in
  inChannel usr chn $ serveS ctx [Join usr chn]

prop_all_members_get_join_message :: Commands -> User -> User -> Channel -> Bool
prop_all_members_get_join_message cs usr joiner chn =
  let ctx = serve (cs ++ [Join usr chn]) in
  inResponses (Evn_Join usr joiner chn) $ serveR ctx [Join joiner chn]

prop_joiner_gets_message :: Commands -> User -> Channel -> Bool
prop_joiner_gets_message cs usr chn =
  let ctx = serve cs in
  inResponses (Evn_Join usr usr chn) $ serveR ctx [Join usr chn]

prop_part_implies_not_in_channel :: Commands -> User -> Channel -> Bool
prop_part_implies_not_in_channel cs usr chn =
  let ctx = serve cs in
  not $ inChannel usr chn $ serveS ctx [Part usr chn]

prop_all_members_get_part_message :: Commands -> User -> User -> Channel -> Bool
prop_all_members_get_part_message cs usr parter chn =
  let ctx = serve (cs ++ [Join usr chn]) in
  inResponses (Evn_Part usr parter chn) $ serveR ctx [Part parter chn]

prop_parter_gets_message :: Commands -> User -> Channel -> Bool
prop_parter_gets_message cs usr chn =
  let ctx = serve cs in
  inResponses (Evn_Part usr usr chn) $ serveR ctx [Part usr chn]

prop_part_left_inverse_of_join :: Commands -> User -> Channel -> Bool
prop_part_left_inverse_of_join cs usr chn =
  let ctx = serve (cs ++ [Part usr chn]) in
  snd (serve' ctx [Join usr chn, Part usr chn]) == snd ctx

prop_all_members_get_privmsg_message :: Commands -> User -> User -> Channel -> String -> Bool
prop_all_members_get_privmsg_message cs usr sender chn msg =
  let ctx = serve (cs ++ [Join usr chn, Join sender chn]) in
  inResponses (Evn_Privmsg usr sender chn msg) $ serveR ctx [Privmsg sender chn msg]

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
