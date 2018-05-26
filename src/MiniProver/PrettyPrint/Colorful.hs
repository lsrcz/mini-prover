module MiniProver.PrettyPrint.Colorful (
    Color(..)
  , frontGroundColor
  , backGroundColor
  , bright
  , underline
  ) where

data Color =
    BLACK
  | RED
  | GREEN
  | YELLOW
  | BLUE
  | MAGENTA
  | CYAN
  | WHITE
  | BBLACK
  | BRED
  | BGREEN
  | BYELLOW
  | BBLUE
  | BMAGENTA
  | BCYAN
  | BWHITE
  deriving (Show)

addAttribute :: Int -> String -> String
addAttribute a str = "\x1b[" ++ show a ++ "m" ++ str ++ "\x1b[0m"

colorToFrontGroundCode :: Color -> Int
colorToFrontGroundCode c =
  case c of
    BLACK      -> 30
    RED        -> 31
    GREEN      -> 32
    YELLOW     -> 33
    BLUE       -> 34
    MAGENTA    -> 35
    CYAN       -> 36
    WHITE      -> 37
    BBLACK     -> 90
    BRED       -> 91
    BGREEN     -> 92
    BYELLOW    -> 93
    BBLUE      -> 94
    BMAGENTA   -> 95
    BCYAN      -> 96
    BWHITE     -> 97

-- will go wrong sometimes when nested, but it's enough for the task
frontGroundColor :: Color -> String -> String
frontGroundColor = addAttribute . colorToFrontGroundCode

backGroundColor :: Color -> String -> String
backGroundColor = addAttribute . (+10) . colorToFrontGroundCode

bright :: String -> String
bright = addAttribute 1

underline :: String -> String
underline = addAttribute 4
