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
partChannel' usr chn ((chn' , usrs) : xs) = if chn == chn'
  then (chn' , delete usr usrs) : xs
  else (chn' , usrs) : partChannel' usr chn xs

respond :: Command -> State -> (Responses , State)
respond (Join usr chn) xs = (joinChannel usr chn xs , joinChannel' usr chn xs)
respond (Part _ _) _ = undefined
respond (Privmsg _ _ _) _ = undefined

{- Properties -}

prop_joiner_gets_message :: User -> Channel -> Users -> Bool
prop_joiner_gets_message usr chn usrs =
  inResponses (Evn_Join usr usr chn) (map (\x -> Evn_Join x usr chn) (usr : usrs))

prop_join_implies_in_channel :: User -> Channel -> State -> Bool
prop_join_implies_in_channel usr chn xs =
  inChannel usr chn (joinChannel' usr chn xs)

prop_all_members_get_join_message :: User -> User -> Channel -> State -> Property
prop_all_members_get_join_message usr joiner chn xs =
  let xs' = joinChannel' usr chn xs in
  inChannel usr chn xs' ==>
  inResponses (Evn_Join usr joiner chn) (joinChannel joiner chn xs')

main :: IO ()
main = do
  smallCheck 4 prop_joiner_gets_message
  smallCheck 3 prop_join_implies_in_channel
  smallCheck 3 prop_all_members_get_join_message
  putStrLn "Done!"
