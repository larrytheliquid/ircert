module Ircert where

type User = Int
type Channel = Int

data Command =
   Join User Channel
 | Part User Channel
 | Privmsg User Channel String

data Response =
   Evn_Join User User Channel
  deriving Eq

type Users = [User]
type Responses = [Response]
type State = [(Channel , Users)]

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

joinChannel :: User -> Channel -> State -> Responses
joinChannel usr chn xs = map (\x -> Evn_Join x usr chn) (usr : members chn xs)

