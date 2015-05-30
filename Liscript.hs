module Liscript where

import qualified Data.Map.Strict as Map
import Data.IORef
import System.IO
import Data.Time


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
eqVal (Atom a)  (Atom b)  = a==b
eqVal (List []) (List []) = True -- тут конечно надо сравнить поэлементно
eqVal _         _         = False


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


eval :: Env -> LispVal -> IO LispVal
eval env (Atom s) = getVar env s
eval env (List l) = do
    op <- eval env $ head l
    let ls = tail l

        foldInteger op = do
            evls <- mapM (eval env) ls
            let l = map ((\s -> read s::Integer) . fromAtom) evls
            return $ Atom $ show $ foldl1 op l

        foldDouble op = do
            evls <- mapM (eval env) ls
            let l = map ((\s -> read s::Double) . fromAtom) evls
            return $ Atom $ show $ foldl1 op l

        compareInteger op = do
            evls <- mapM (eval env) $ take 2 ls
            let [a,b] = map ((\s -> read s::Integer) . fromAtom) evls
            return $ Atom $ show $ op a b

        compareDouble op = do
            evls <- mapM (eval env) $ take 2 ls
            let [a,b] = map ((\s -> read s::Double) . fromAtom) evls
            return $ Atom $ show $ op a b

    case op of

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
            value <- eval env $ head ls
            let go (Atom _) = Atom "True"
                go _        = Atom "False"
            return $ go value

        Atom "list?" -> do
            value <- eval env $ head ls
            let go (List _) = Atom "True"
                go _        = Atom "False"
            return $ go value

        Atom "eq?" -> do
            [a,b] <- mapM (eval env) $ take 2 ls
            return $ Atom . show $ (==) a b

        Atom "quote" -> return $ head ls

        Atom "eval" -> do
            value <- eval env $ head ls
            eval env value

        Atom "str" -> do
            evls <- mapM (eval env) ls
            return $ List evls

        Atom "cond" -> do
            let cond (p:e:xx) = do
                    evp <- eval env p
                    if (\s -> read s::Bool) . fromAtom $ evp
                        then eval env e else cond xx
                cond [e] = eval env e
            cond ls

        Atom "printLn" -> do
            value <- eval env $ head ls
            putStrLn $ show value
            return $ Atom ""

        Atom "print" -> do
            value <- eval env $ head ls
            putStr $ show value
            return $ Atom ""

        Atom "set!" -> do
            value <- eval env $ last ls
            setVar env (fromAtom . head $ ls) value
            return $ Atom ""

        Atom "def" -> do
            value <- eval env $ last ls
            defVar env (fromAtom . head $ ls) value
            return $ Atom ""

        Atom "defn" -> do
            value <- eval env $ List $ (Atom "lambda") : tail ls
            defVar env (fromAtom . head $ ls) value
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
            evls <- mapM (eval env) ls
            let cons x (List l)  = List (x:l)
--                cons x (Atom  s) = List (x:(Atom s):[])
                cons x y = List (x:y:[])
            return $ cons (evls!!0) (evls!!1)

        Atom "car" -> do
            value <- eval env $ head ls
            let car (List l)  = if null l then List [] else head l
                car (Atom  s) = Atom ""
            return $ car value

        Atom "cdr" -> do
            value <- eval env $ head ls
            let cdr (List l)  = if null l then List [] else List (tail l)
                cdr (Atom  s) = Atom ""
            return $ cdr value

        Func {params = args, body = foobody, closure = envfun} -> do
            evls <- mapM (eval env) ls
            reflocalframe <- newIORef $ Map.fromList $ zip args evls
            let envloc = Voc (reflocalframe, envfun)
            eval envloc $ List foobody

        Macr {params = args, body = macrobody} -> do
            let body' = foldr macroexpand (List macrobody) $ zip args ls
--            print body'
            eval env $ body'

        _ -> do
            let go []  = return op
                go [x] = eval env x
                go (x:xs) = do
                    eval env x
                    go xs
            go ls


------------------------------- МЭЙН -------------------------------


loadfile env filename = do
    handle   <- openFile filename ReadMode
    contents <- hGetContents handle
    res      <- eval env . str2LV . prepare $ contents
    print res
    hClose handle
    return res

main = do
    begT <- getCurrentTime

    refglobalframe <- newIORef $ Map.empty
    let globalframe = Voc (refglobalframe, NullEnv)

    loadfile globalframe "lib.txt"
    loadfile globalframe "test.txt"

    endT <- getCurrentTime
    putStrLn $ "Elapced time: " ++ show (diffUTCTime endT begT)


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
