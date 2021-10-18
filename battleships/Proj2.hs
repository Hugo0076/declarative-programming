--  File     : Proj2.hs
--  Author   : Hugo Lyons Keenan 1081696 <hlyonskeenan@student.unimelb.edu.au>
--  Purpose  : Implementations of the functions and types required for Project 2

-- | The first call is made to initialGuess, it always returns the guess 
-- [G2, H3, H4] and the full GameState containing all the possible targets 
-- (see definition for GameState for more info.) For a more in-depth explanation
-- of why this guess is chosen, see the appendix at the end of this file. After 
-- the initial guess is made, we receive feedback and are asked to make the next
-- guess. Two steps are taken: first, all of the targets that produce feedback
-- different to what we recieved are discarded from the GameState as they cannot
-- possibly be the true target. Secondly, we choose the guess with the lowest
-- expected number of targets remaining after feedback for it is received. When
-- the symmetry trick described in hint 6 is implemented, the program is able to
-- guess the target in a consistently low number of guesses while being
-- appropriately time efficient. 

module Proj2 (Location, toLocation, fromLocation, feedback,
              GameState, initialGuess, nextGuess) where              
import Data.Char
import Data.List
import Data.Function
import System.Exit (exitSuccess)

-- | Location data type definition. A very simple implementation where each
-- location has only a Char and Int representing its x and y coordinate
-- respectively. Eq is derived and Show is mapped to fromLocation (defined 
-- later.)
data Location = Location Char Int
  deriving Eq
instance Show Location where show = fromLocation

-- | GameState data type definition. Again a very simple implementation, each
-- game state has an Int representing the number of turns (not explicitly used 
-- in the current algorithm) and a list of potential targets (list of locations)
-- that is cut down as the program receives more information about the true
-- target. Show is derived.
data GameState = GameState Int [[Location]]
  deriving Show

-- | toLocation function implemtation. Converts a string such as "A4" to 'Just 
-- the corresponding location type. If the string passed is not valid, returns
-- Nothing.
toLocation :: String -> Maybe Location
toLocation str
  | length str /= 2 = Nothing
  | x `elem` xs && y `elem` ys = Just (Location x y)
  | otherwise = Nothing
  where x = (str !! 0)
        y = digitToInt (str !! 1)
        xs = ['A'..'H']
        ys = [1..4]

-- | fromLocation function implemtation. Converts a Location type to a 
-- representative string. Does not perform validity checking.
fromLocation :: Location -> String
fromLocation (Location x y) = [x] ++ (show y)

-- | feedback function implemtation. Given a guess and target, return feedback 
-- as specified in the problem description. This function works by calling the
-- helper funciton feedback1 on each element of the guess.
feedback :: [Location] -> [Location] -> (Int,Int,Int)
feedback target guess = 
  foldr (\(x,y,z) (x',y',z') -> (x+x',y+y',z+z')) (0,0,0) 
    [feedback1 target g | g <- guess]

-- | Given an element of a guess (a location) and a target, return feedback for 
-- that element.
feedback1 :: [Location] -> Location -> (Int,Int,Int)
feedback1 targets guess 
  | guess `elem` targets = (1,0,0)
  | (neighbours 1 guess) `intersect` targets /= [] = (0,1,0)
  | (neighbours 2 guess) `intersect` targets /= [] = (0,0,1)
  | otherwise = (0,0,0)

-- | Given a Location, determine if it is valid and return the result as a Bool.
valid :: Location -> Bool
valid (Location x y)
  | x `elem` xs && y `elem` ys = True
  | otherwise = False
  where xs = ['A'..'H']
        ys = [1..4]

-- | Given a radius d and a Location, return all of the valid neighbours of 
-- the Location of distance d or less in all ordinal directions.
neighbours :: Int -> Location -> [Location]
neighbours d (Location x y) = 
  [Location x' y' |x' <- xs, y' <- ys, valid (Location x' y')]
    where xs = [x_s..x_e]
          ys = [y_s..y_e]
          x_s = chr $ ord x - d
          x_e = chr $ ord x + d
          y_s = y - d
          y_e = y + d

-- | initialGuess function implemtation. Returns the inital guess and an initial
-- GameState that has all the possible targets included in it. For a more 
-- in-depth explanation of why this guess is chosen, see the appendix at the end
-- of this file.
initialGuess :: ([Location],GameState)
initialGuess = (initial, GameState 0 allGuesses)
  where allGuesses = comb 3 allLocs
        allLocs = [Location x' y' |x' <- xs, y' <- ys]
        xs = ['A'..'H']
        ys = [1..4]
        initial = [(Location 'G' 2),(Location 'H' 3),(Location 'H' 4)]

-- | Given a previous guess, GameState and feedback for the guess, returns an 
-- updated GameState that contains only the targets that could have produced the
-- feedback.
updateGS :: ([Location],GameState) -> (Int,Int,Int) -> GameState
updateGS (guess,(GameState n possible)) fb = (GameState (n+1) remaining)
  where remaining = [t | t <- possible , feedback t guess == fb]

-- | nextGuess function implemtation. Given a previous guess, GameState and 
-- feedback for the guess, returns the next guess and an updated GameState.
nextGuess :: ([Location],GameState) -> (Int,Int,Int) -> ([Location],GameState)
nextGuess prevInfo fb = (nGuess,newGS)
  where newGS = updateGS prevInfo fb
        nGuess = makeGuess remaining 
        remaining = getRemaining newGS 

-- | Extracts the remaining targets from a GameState.
getRemaining :: GameState -> [[Location]]
getRemaining (GameState _ remaining) = remaining

-- | Given a number of possible targets, returns the guess that gives the 
-- greatest expected reduction in the remaining number of targets. 
makeGuess :: [[Location]] -> [Location]
makeGuess guesses = snd $ (sortBy (compare `on` fst) lstEV) !! 0 
  where lstEV = [(calcEG guess guesses, guess)| guess <- guesses]

-- | Given a number of possible targets and a guess, calculates the expected
-- number of remaining targets after the guess is made. We can reduce the 
-- computational complexity of this calcualtion by realising that the 
-- probability of any particular feedback being recieved is just count(fb)/N if 
-- we assume an equal distribution of targets. This makes the expected value 
-- computation much quicker. 
calcEG :: [Location] -> [[Location]] -> Float
calcEG guess guesses = (sumEV) / (fromIntegral len)
  where counts = map length (group fblist) 
        sumEV = sum [(fromIntegral count)^2| count <- counts]
        fblist = sort [feedback target guess | target <- guesses]
        len = length fblist

-- | Produces all of the combinations of size n for a given list, xs. 
comb :: Int -> [Location] -> [[Location]]
comb n xs = comb_s xs !! (l-n)
  where l = length xs

-- | Helper function for 'comb'. Produces a list of all of the combinations for
-- a given list xs in order their size. 
comb_s :: [Location] -> [[[Location]]]
comb_s [] = [[[]]]
comb_s (x:xs) = zipWith (++) ([]:next) (map (map (x:)) next ++ [[]]) 
  where  next = comb_s xs
  
--  APPENDIX

-- | Explanation of initial guess choice
-- To find the best initial guess, functions were created that tested every
-- initial guess and found the one that had the lowest maximum number of
-- potential targets. For example, the initial guess [H1,H2,H3] returns this 
-- feedback over all possible targets:
-- [(1140,(0,0,0)),(0,(0,0,1)),(190,(0,0,2)),(0,(0,1,0)),(441,(0,1,1))...]
-- where the first element of the tuple is the number of targets producing the
-- feedback in the second element of the tuple. As the initial guess sets up the
-- state that the next guess works with, it is important to optimise the initial
-- guess to guarantee that the program will only need to look at X potential 
-- targets for guess 2 and subsequent guesses. the initial guess [G2, H3, H4] 
-- ensures we have a maximum of 639 potential targets to calculate the optimal
-- guess over in guess 2, which in turn means our progam will not run over time.
-- the functions used to generate the list of (max, guess) tuples is below.

initialGuess2 :: [Location] ->([Location],GameState)
initialGuess2 initial = (initial, GameState 0 allGuesses)
    where allGuesses = comb 3 allLocs
          allLocs = [Location x' y' |x' <- xs, y' <- ys]
          xs = ['A'..'H']
          ys = [1..4]

testr :: [Location] -> Int
testr guess =  maximum list
  where list = [length (getRemaining (updateGS (initialGuess2 guess) (a,b,c)))|
            a <- [0..2], b <- [0..2], c <- [0..2], a+b+c < 4]
            
testall :: [(Int, [Location])]
testall = [(testr guess, guess)|guess <- initguesses]
    where initguesses = comb 3 allLocs
          allLocs = [Location x' y' |x' <- xs, y' <- ys]
          xs = ['A'..'H']
          ys = [1..4]


