module Parser where
import Text.ParserCombinators.Parsec
import Ircert

message usr = many (
      try (join usr)
  <|> try (part usr)
  <|> try (privmsg usr)
  <|> unknown usr
  )

join usr = do
  string "JOIN"
  sp
  chn <- channel
  crlf
  return $ Join usr chn

part usr = do
  string "PART"
  sp
  chn <- channel
  crlf
  return $ Part usr chn

privmsg usr = do
  string "PRIVMSG"
  sp
  chn <- channel
  sp
  msg <- body
  crlf
  return $ Privmsg usr chn msg

unknown usr = do
  cmd <- many alphaNum
  sp
  many $ noneOf "\r\n"
  crlf
  return $ Unknown usr cmd

channel = char '#' >> chanstring
chanstring = many alphaNum
body = char ':' >> many alphaNum
sp = char ' '
cr = char '\r'
lf = char '\n'
crlf = cr >> lf

parseIRC :: User -> String -> Either ParseError Commands
parseIRC usr input = parse (message usr) "(unknown)" input


