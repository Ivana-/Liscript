--module Liscript where

import Data.Maybe (fromMaybe)
import Control.Monad
import qualified Data.Map.Strict as Map
import Data.IORef
import System.IO
import Data.Time
import GHC.IO.Encoding --(setLocaleEncoding, utf8)


------------------------ ТИП LispVal И ЕГО ИНСТАНСЫ ---------------------


data LispVal = Atom String
             | List [LispVal]
             | Func { params :: [String], body :: [LispVal], closure :: Env }
             | Macr { params :: [String], body :: [LispVal] }

instance Show LispVal where show = showVal
instance Eq   LispVal where (==) = eqVal

showVal :: LispVal -> String
showVal (Atom contents) = contents
showVal (List contents) = "(" ++ unwords (map showVal contents) ++ ")"
showVal (Func {params = args, body = body, closure = _}) = "(LAMBDA "
    ++ unwords (map show args)  ++ " (" ++ unwords (map showVal body) ++ "))"
showVal (Macr {params = args, body = body}) = "(MACRO "
    ++ unwords (map show args)  ++ " (" ++ unwords (map showVal body) ++ "))"

eqVal :: LispVal -> LispVal -> Bool
eqVal (Atom a) (Atom b) = a == b
eqVal (List [])     (List [])     = True
eqVal (List (a:_))  (List [])     = False
eqVal (List [])     (List (b:_))  = False
eqVal (List (a:as)) (List (b:bs)) = eqVal a b && eqVal (List as) (List bs)
eqVal (Macr {params = a1, body = b1}) (Macr {params = a2, body = b2}) =
    a1 == a2 && eqVal (List b1) (List b2)
eqVal _  _ = False


------------------------------- ОКРУЖЕНИЕ -------------------------------


type Frame = Map.Map String LispVal -- кадр связывания имен ключ-значение
data Env = NullEnv | Voc (IORef Frame, Env) -- дерево кадров текущий-родитель

setVar NullEnv                  _   value = return ()
setVar (Voc (refframe, parenv)) var value = do
    frame <- readIORef refframe
    if Map.member var frame then modifyIORef' refframe $ Map.insert var value
    else setVar parenv var value

getVar NullEnv                  var = return $ Atom var
getVar (Voc (refframe, parenv)) var = readIORef refframe >>=
    maybe (getVar parenv var) return . Map.lookup var

defVar NullEnv                  _   value = return ()
defVar (Voc (refframe, parenv)) var value = modifyIORef' refframe $ Map.insert var value


------------------------------- ПАРСЕР -------------------------------


mytokens :: String -> [String]
mytokens = go 0 False "" where
    go _ _ t [] = addtoken t []
    go l f t (c:cs)
        | elem c " \n\t" && l==0 && not f = addtoken t $ go 0 False "" cs
        | otherwise = go l' f' (c:t) cs
        where
            l' | f = l | c=='(' = l+1 | c==')' = l-1 | otherwise = l
            f' | c=='"' = not f | otherwise = f
    addtoken t r | null t = r | otherwise = reverse t:r

str2LV :: String -> LispVal
str2LV = go . mytokens where
    go [t] | fst == '(' && lst == ')' = List . map str2LV . mytokens $ mid
           | fst == '"' && lst == '"' = Atom mid
           | fst == '\'' = List $ Atom "quote" : [str2LV $ tail t]
           | otherwise = Atom t
        where fst = head t
              lst = last t
              mid = tail $ init t
    go l = List $ map str2LV l

fromAtom (Atom s) = s
prepare = id -- можно написать замену "(" на " (" и т.п. перед парсингом


------------------------------ МАКРОСЫ -----------------------------


macroexpand :: [(String, LispVal)] -> LispVal -> LispVal
macroexpand kv = go where
    go (Atom a) = fromMaybe (Atom a) $ lookup a kv
    go (List l) = List $ map go l
    go        x = x


------------------------------- ЭВАЛ -------------------------------


eval :: Handle -> Env -> LispVal -> IO LispVal
eval hFile env (Atom s) = getVar env s
eval hFile env (List l) = do

    let ls = tail l

        listOrVal [v] = v
        listOrVal  l  = List l

        zipArgsVals []      _ = []
        zipArgsVals  _     [] = []
        zipArgsVals [a]     b = [(a, listOrVal b)]
        zipArgsVals (a:as) (b:bs) = (a, b) : zipArgsVals as bs

        evls = mapM (eval hFile env) ls

        str2Int s = read s :: Integer
        str2Dou s = read s :: Double
        foldOp op t = evls >>= return . Atom . show . foldl1 op . map (t . fromAtom)
        compOp op t = evls >>= return . Atom . show . go . map (t . fromAtom) where
            go (a:b:xx) = op a b && go (b:xx)
            go _ = True

    op <- eval hFile env $ head l
    case op of

        Atom "++" -> foldOp (++) id

        Atom "+" -> foldOp (+) str2Int
        Atom "-" -> foldOp (-) str2Int
        Atom "*" -> foldOp (*) str2Int
        Atom "/" -> foldOp div str2Int
        Atom "mod" -> foldOp mod str2Int

        Atom "+'" -> foldOp (+) str2Dou
        Atom "-'" -> foldOp (-) str2Dou
        Atom "*'" -> foldOp (*) str2Dou
        Atom "/'" -> foldOp (/) str2Dou

        Atom ">"  -> compOp (>) str2Int
        Atom ">=" -> compOp (>=) str2Int
        Atom "<"  -> compOp (<) str2Int
        Atom "<=" -> compOp (<=) str2Int
        Atom "="  -> compOp (==) str2Int
        Atom "/=" -> compOp (/=) str2Int

        Atom ">'"  -> compOp (>) str2Dou
        Atom ">='" -> compOp (>=) str2Dou
        Atom "<'"  -> compOp (<) str2Dou
        Atom "<='" -> compOp (<=) str2Dou
        Atom "='"  -> compOp (==) str2Dou
        Atom "/='" -> compOp (/=) str2Dou

        Atom "eq?" -> evls >>= return . Atom . show . (\l -> all (==head l) l)

        Atom "quote" -> return $ listOrVal ls

        Atom "eval" -> evls >>= mapM (eval hFile env) >>= return . listOrVal

        Atom "str" -> evls >>= return . List

        Atom "strTolist" -> evls >>= return . List . map (Atom.(:"")) . concatMap fromAtom

        Atom "cond" -> cond ls where
            cond (p:e:xx) = eval hFile env p >>=
                \p -> if (read $ fromAtom p) then eval hFile env e else cond xx
            cond [e]      = eval hFile env e
            cond []       = return $ Atom ""

        Atom "while" -> while ls where
            while px@(p:xx) = eval hFile env p >>= \p -> if (read $ fromAtom p)
                then eval hFile env (List xx) >> while px else return $ Atom ""

        Atom "printLn" -> evls >>=
            mapM_ ((if printToFile then hPutStrLn hFile else putStrLn) . show) >> return (Atom "")

        Atom "print" -> evls >>=
            mapM_ ((if printToFile then hPutStr hFile else putStr) . show) >> return (Atom "")

        Atom "def" -> go ls where
            go (n:e:xx) = eval hFile env e >>= defVar env (fromAtom n) >> go xx
            go _ = return $ Atom ""

        Atom "name-def" -> evls >>= go where
            go (n:v:xx) = defVar env (fromAtom n) v >> go xx
            go _ = return $ Atom ""

        Atom "set!" -> go ls where
            go (n:e:xx) = eval hFile env e >>= setVar env (fromAtom n) >> go xx
            go _ = return $ Atom ""

        Atom "name-set!" -> evls >>= go where
            go (n:v:xx) = setVar env (fromAtom n) v >> go xx
            go _ = return $ Atom ""

--        Atom "defn" -> eval hFile env (List $ (Atom "lambda") : tail ls) >>=
--            defVar env (fromAtom . head $ ls) >> return (Atom "")

        Atom "cons" -> evls >>= return . foldr1 cons where
            cons x (List l) = List (x:l)
            cons x y        = List [x,y]

        Atom "car" -> eval hFile env (head ls) >>= return . car where
            car (List l) = if null l then List [] else head l
            car x = x

        Atom "cdr" -> eval hFile env (head ls) >>= return . cdr where
            cdr (List l) = if null l then List [] else List (tail l)
            cdr _ = List []

        Atom x | x == "lambda"-> return Func { params = args, body = foobody, closure = env }
               | x == "macro" -> return Macr { params = args, body = foobody }
            where args = (\(List l) -> map fromAtom l) $ head ls
                  getbody [List a] = getbody a
                  getbody l = l
                  foobody  = getbody $ tail ls

        Atom x | x `elem` ["atom?", "list?", "func?", "macr?"] ->
            evls >>= return . Atom . show . all tst where
                tst = (==x) . gettype
                gettype (Atom _) = "atom?"
                gettype (List _) = "list?"
                gettype (Func { params = _, body = _, closure = _ }) = "func?"
                gettype (Macr { params = _, body = _ }) = "macr?"

        Func {params = args, body = foobody, closure = envfun} -> do
            reflocalframe <- evls >>= newIORef . Map.fromList . zipArgsVals args
            eval hFile (Voc (reflocalframe, envfun)) $ List foobody

        Macr {params = args, body = macrobody} -> eval hFile env
                . macroexpand (zipArgsVals args ls) $ List macrobody

        _ -> go ls where
            go []     = return op
            go [x]    = eval hFile env x
            go (x:xs) = eval hFile env x >> go xs


------------------------------- МЭЙН -------------------------------


loadfile hFile env filename = do
    handle   <- openFile filename ReadMode
    hSetEncoding handle utf8
    contents <- hGetContents handle
    res      <- eval hFile env . str2LV . prepare $ contents
    print res
    hClose handle
    return res

printToFile = False --True

main = do
    setLocaleEncoding utf8
    begT <- getCurrentTime

    refglobalframe <- newIORef Map.empty
    let globalframe = Voc (refglobalframe, NullEnv)

    hOutFile <- openFile "rezult_Liscript.txt" WriteMode

    loadfile hOutFile globalframe "lib.txt"
    loadfile hOutFile globalframe "test.txt"
    loadfile hOutFile globalframe "test1.txt"
--    loadfile hOutFile globalframe "test2.txt"
--    loadfile hOutFile globalframe "test3.txt"
--    loadfile hOutFile globalframe "solveWK.txt"
--    loadfile hOutFile globalframe "testWKsmall.txt"
--    loadfile hOutFile globalframe "testWK.txt"

    hClose hOutFile

    endT <- getCurrentTime
    putStrLn $ "Elapced time: " ++ show (diffUTCTime endT begT)
    --_ <- getLine
    --putStr ""


-- дополнительные необязательные функции
-- если для отладки надо посмотреть содержимое окружения

showEnv NullEnv                  = putStr "Null"
showEnv (Voc (refframe, parenv)) = do
    putStr "("
    frame <- readIORef refframe
    putStr $ show frame
    putStr ","
    showEnv parenv
    putStr ")"

myprint f@(Func {params = _, body = _, closure = env}) = do
    print f
    showEnv env
    putStrLn ""
myprint x = print x
