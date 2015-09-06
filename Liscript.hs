--module Liscript where

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
getVar (Voc (refframe, parenv)) var = do
    frame <- readIORef refframe
    maybe (getVar parenv var) return $ Map.lookup var frame

defVar NullEnv                  _   value = return ()
defVar (Voc (refframe, parenv)) var value = do
    modifyIORef' refframe $ Map.insert var value


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
           | fst == '\'' = List $ (Atom "quote") : [str2LV $ tail t]
           | otherwise = Atom t
        where fst = head t
              lst = last t
              mid = tail $ init t
    go l = List $ map str2LV l

fromAtom (Atom s) = s
prepare = id -- можно написать замену "(" на " (" и т.п. перед парсингом


------------------------------ МАКРОСЫ -----------------------------


macroexpand :: (String, LispVal) -> LispVal -> LispVal
macroexpand varval body = go body where
    (var, val) = varval
    go (Atom a) | a==var = val | otherwise = (Atom a)
    go (List l) = List $ map go l
    go        x = x


------------------------------- ЭВАЛ -------------------------------


eval :: Handle -> Env -> LispVal -> IO LispVal
eval hFile env (Atom s) = getVar env s
eval hFile env (List l) = do
    op <- eval hFile env $ head l
    let ls = tail l

        foldString op = do
            evls <- mapM (eval hFile env) ls
            let l = map fromAtom evls
            return $ Atom $ show $ foldl1 op l

        foldInteger op = do
            evls <- mapM (eval hFile env) ls
            let l = map ((\s -> read s::Integer) . fromAtom) evls
            return $ Atom $ show $ foldl1 op l

        foldDouble op = do
            evls <- mapM (eval hFile env) ls
            let l = map ((\s -> read s::Double) . fromAtom) evls
            return $ Atom $ show $ foldl1 op l

        compareInteger op = do
            evls <- mapM (eval hFile env) $ take 2 ls
            let [a,b] = map ((\s -> read s::Integer) . fromAtom) evls
            return $ Atom $ show $ op a b

        compareDouble op = do
            evls <- mapM (eval hFile env) $ take 2 ls
            let [a,b] = map ((\s -> read s::Double) . fromAtom) evls
            return $ Atom $ show $ op a b

    case op of

        Atom "++" -> foldString (++)

        Atom "+" -> foldInteger (+)
        Atom "-" -> foldInteger (-)
        Atom "*" -> foldInteger (*)
        Atom "/" -> foldInteger (div)
        Atom "mod" -> foldInteger (mod)

        Atom "+'" -> foldDouble (+)
        Atom "-'" -> foldDouble (-)
        Atom "*'" -> foldDouble (*)
        Atom "/'" -> foldDouble (/)

        Atom ">"  -> compareInteger (>)
        Atom ">=" -> compareInteger (>=)
        Atom "<"  -> compareInteger (<)
        Atom "<=" -> compareInteger (<=)
        Atom "="  -> compareInteger (==)
        Atom "/=" -> compareInteger (/=)

        Atom ">'"  -> compareDouble (>)
        Atom ">='" -> compareDouble (>=)
        Atom "<'"  -> compareDouble (<)
        Atom "<='" -> compareDouble (<=)
        Atom "='"  -> compareDouble (==)
        Atom "/='" -> compareDouble (/=)

        Atom "atom?" -> do
            value <- eval hFile env $ head ls
            let go (Atom _) = Atom "True"
                go _        = Atom "False"
            return $ go value

        Atom "list?" -> do
            value <- eval hFile env $ head ls
            let go (List _) = Atom "True"
                go _        = Atom "False"
            return $ go value

        Atom "eq?" -> do
            [a,b] <- mapM (eval hFile env) $ take 2 ls
            return $ Atom . show $ (==) a b

        Atom "quote" -> return $ head ls

        Atom "eval" -> do
            value <- eval hFile env $ head ls
            eval hFile env value

        Atom "str" -> do
            evls <- mapM (eval hFile env) ls
            return $ List evls

        Atom "strTolist" -> do
            --evls <- mapM (eval hFile env) ls
            return . List . map (Atom.(:"")) . concatMap fromAtom =<< mapM (eval hFile env) ls

        Atom "cond" -> do
            let cond (p:e:xx) = do
                    evp <- eval hFile env p
                    if (\s -> read s::Bool) . fromAtom $ evp
                        then eval hFile env e else cond xx
                cond [e] = eval hFile env e
            cond ls

        Atom "while" -> do
            let while px@(p:xx) = do
                    evp <- eval hFile env p
                    if (\s -> read s::Bool) . fromAtom $ evp then do
                        _ <- eval hFile env $ List xx
                        while px
                    else return $ Atom ""
            while ls

        Atom "printLn" -> do
            value <- eval hFile env $ head ls
            if printToFile then hPutStrLn hFile (show value) else putStrLn (show value)
            return $ Atom ""

        Atom "print" -> do
            value <- eval hFile env $ head ls
            if printToFile then hPutStr hFile (show value) else putStr (show value)
            return $ Atom ""

        Atom "set!" -> do
--            name  <- eval hFile env $ head ls
            value <- eval hFile env $ last ls
            setVar env (fromAtom . head $ ls) value
--            setVar env (fromAtom name) value
            return $ Atom ""

        Atom "name-set!" -> do
            name  <- eval hFile env $ head ls
            value <- eval hFile env $ last ls
--            setVar env (fromAtom . head $ ls) value
            setVar env (fromAtom name) value
            return $ Atom ""

        Atom "def" -> do
--            name  <- eval hFile env $ head ls
            value <- eval hFile env $ last ls
            defVar env (fromAtom . head $ ls) value
--            defVar env (fromAtom name) value
            return $ Atom ""

        Atom "name-def" -> do
            name  <- eval hFile env $ head ls
            value <- eval hFile env $ last ls
            defVar env (fromAtom name) value
            return $ Atom ""

        Atom "defn" -> do
--            name  <- eval hFile env $ head ls
            value <- eval hFile env $ List $ (Atom "lambda") : tail ls
            defVar env (fromAtom . head $ ls) value
--            defVar env (fromAtom name) value
            return $ Atom ""

        Atom "lambda" -> do
            let
                getargnames (List l) = map fromAtom l
                args = getargnames $ head ls
                getfoobody [List a] = getfoobody a
                getfoobody l = l
                foobody  = getfoobody $ tail ls
            return Func { params = args, body = foobody, closure = env }

        Atom "macro" -> do
            let
                getargnames (List l) = map fromAtom l
                args = getargnames $ head ls
                getmacrobody [List a] = getmacrobody a
                getmacrobody l = l
                macrobody  = getmacrobody $ tail ls
            return Macr { params = args, body = macrobody }

        Atom "cons" -> do
            evls <- mapM (eval hFile env) ls
            let cons x (List l)  = List (x:l)
--                cons x (Atom  s) = List (x:(Atom s):[])
                cons x y = List (x:y:[])
            return $ cons (evls!!0) (evls!!1)

        Atom "car" -> do
            value <- eval hFile env $ head ls
            let car (List l)  = if null l then List [] else head l
                car (Atom  s) = Atom ""
            return $ car value

        Atom "cdr" -> do
            value <- eval hFile env $ head ls
            let cdr (List l)  = if null l then List [] else List (tail l)
                cdr (Atom  s) = Atom ""
            return $ cdr value

        Func {params = args, body = foobody, closure = envfun} -> do
            evls <- mapM (eval hFile env) ls
            reflocalframe <- newIORef $ Map.fromList $ zip args evls
            let envloc = Voc (reflocalframe, envfun)
            eval hFile envloc $ List foobody

        Macr {params = args, body = macrobody} -> do
            let body' = foldr macroexpand (List macrobody) $ zip args ls
--            print body'
            eval hFile env $ body'

        _ -> do
            let go []  = return op
                go [x] = eval hFile env x
                go (x:xs) = do
                    eval hFile env x
                    go xs
            go ls


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

    refglobalframe <- newIORef $ Map.empty
    let globalframe = Voc (refglobalframe, NullEnv)

    hOutFile <- openFile "rezult_Liscript.txt" WriteMode

    loadfile hOutFile globalframe "lib.txt"
--    loadfile hOutFile globalframe "test.txt"
--    loadfile hOutFile globalframe "test1.txt"
--    loadfile hOutFile globalframe "test2.txt"
    loadfile hOutFile globalframe "test3.txt"
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
