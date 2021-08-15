module Main where

import Lib
import qualified Data.Set as S
import Data.Set(Set,empty)
--import Data.Attoparsec.Text
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Either (fromLeft,fromRight)
import Control.Monad(join)
import System.TimeIt
import Data.List(sort)

main :: IO ()
main = do
    (n,cnf) <- getCNF
    dpll (n,cnf,S.empty,PARTIAL)
    

getCNF :: IO (Int,CNF)
getCNF = do
    txt <- TIO.readFile "src/example.cnf" 
    let (num,vars) = dimacs txt
        clauses = map (Clause . S.fromList) vars
    return $ (num,S.fromList clauses)

-- DIMACS読み取り簡易パーサー
dimacs :: T.Text -> (Int,[[Int]])
dimacs txt = 
    let p1 = tail $ T.lines txt
        p2 = map T.words p1
        p3 = map (init . map (\x -> read (T.unpack x) :: Int)) p2
        p4 = T.words . head $ T.lines txt
        numOfVars = read (T.unpack $ p4 !! 2) :: Int -- 先頭から三番目
    in (numOfVars,p3)

type Var = Int 
-- DIMACSを活かす上で変数は整数扱いのままの方が好都合
    -- ...のはずだったが、Topを0のシングルトンで扱おうとして混乱したので、Topだけ定数項で表現することに。
data Clause_ a = Clause a | Top deriving(Eq,Ord,Show) 
type Clause = Clause_ (Set Int)
type CNF    = Set Clause
type Singletons = Set Var
type Instance = Set Var
data Flag = SAT | UNSAT | PARTIAL deriving(Eq,Ord) -- 実行中のフラグを定義。初期値はPARTIAL。

-- Functor化。Canonicalな定義。
instance Functor Clause_ where
    fmap f Top = Top
    fmap f (Clause s) = Clause . f $ s

toSet (Clause s) = s

instance Show Flag where
    show SAT     = "SATISFIABLE"
    show UNSAT   = "UNSATISFIABLE"
    show PARTIAL = "It remains to be seen."

-- タプリング法で状態を運用
    -- 第一成分はCNFの現在の状態
    -- 第二成分はSATの場合のインスタンスを溜めていく集合
    -- 第三成分は実行の途中でUNSATが判明したら検知するためのフラグ。これがUNSATになったらそこで終了。
type Tapling = (CNF,Instance,Flag) 


-- 一点集合を判別する関数
isSingleton :: Clause -> Bool
isSingleton Top       = False
isSingleton (Clause s)= if S.size s == 1 
                            then True 
                            else False

isContainingSingleton :: CNF -> Bool
isContainingSingleton cnf =
    let s = S.filter isSingleton cnf
        b = S.size s == 0 -- sのサイズが0ならばSingletonは含まない。0でなければ含む。
    in not b

-- CNF値中のT (= {0})を削除
reduceTop :: CNF -> CNF
reduceTop = S.delete Top



-- CNF値から単項Clauseを回収する関数。
    -- 戻り値が空集合ならばsplitに移行。そうでなければOne-Literalの操作に移行。
getSingletons :: CNF -> Singletons
getSingletons cnf = S.unions . S.map toSet $ S.filter isSingleton cnf -- 単項Clauseだけ残した集合を一つにまとめたもの


-- CNF値に対し簡約操作を実行する関数の中身。
simplify_ :: Var -> Clause -> Clause
simplify_ v Top    = Top
simplify_ v (Clause s) 
    | S.member v s = Top 
    | S.member (-v) s = Clause $ S.delete (-v) s
    | otherwise = Clause s

-- One-Literalの操作に相当。
    -- cnf中の一点集合全てに対してsimplifyする
oneLiteral :: Singletons -> CNF -> CNF
oneLiteral ss cnf =
    if ss == S.empty 
        then cnf
        else 
             let x = S.findMin ss
                 ss' = S.delete x ss
                 cnf' = reduceTop . S.map (simplify_ x) $ cnf -- 確実にTが発生するので、reduceTopで簡約。
             in oneLiteral ss' cnf'


-- 空集合のClauseが含まれるかどうかを判定。
    -- 含まれていたらUNSAT。いなければ続行。
    -- isInconsistentと共に、UNSAT判定に使う。
isContainingEmpty :: CNF -> Bool
isContainingEmpty cnf = S.member (Clause S.empty) cnf

-- cnfの中に空集合が現れたらUNSAT確定、cnf自体が空集合になったらSAT確定、それ以外の時には部分的な判定。
flagCheck :: CNF -> Flag
flagCheck cnf
    | isContainingEmpty cnf = UNSAT
    | cnf == S.empty        = SAT
    | otherwise             = PARTIAL

-- splitにもsimplify_を使う。その第一引数のために、CNF値に含まれるIntの最小値として取得する。
getMinimumVar :: CNF -> Maybe Var
getMinimumVar cnf =
    let findMin' Top = Nothing -- Topは除外
        findMin' (Clause s) =  S.lookupMin s -- 最小値が存在すれば Just n の形で返す。存在しなければNothingを返す
        mins = S.filter (Nothing /=) . S.map findMin' $ cnf  -- 個々の節の最小値でJust nの形をしたものだけを導出
    in join $ S.lookupMin mins --各Clauseの最小値の中から一番小さい値を導出。存在しなければ(minsが空集合ならば)Nothingを返す。

-- splittingの操作の中心部分。getMinimumVarとは分離した。
split_ :: Var -> CNF -> CNF
split_ v cnf = S.map (simplify_ v) cnf

dpll_ :: (CNF,Instance,Flag) -> IO (CNF,Instance,Flag) -- タプリング法を回す関数。Flagのパターンマッチで再帰の基底部を指定。
dpll_ (cnf,inst,UNSAT) = return (cnf,inst,UNSAT)
dpll_ (cnf,inst,SAT)   = return (cnf,inst,SAT)
dpll_ (cnf,inst,PARTIAL)  = 
    let cnf_TopRemoved = reduceTop cnf 
        ss   = getSingletons cnf_TopRemoved
    in if ss /= S.empty
        then let 
                cnf_OneLiteral = oneLiteral ss cnf_TopRemoved
                inst' = S.union ss inst
                flag_OneLiteral = flagCheck cnf_OneLiteral -- cnf_OneLiteralが空集合ならばSAT、空集合を含めばUNSAT。
             in do
                 -- print inst'
                 dpll_ (cnf_OneLiteral, inst', flag_OneLiteral) -- oneLiteral後の再帰
        else let -- cnf_TopRemovedが一点集合を含まない場合
                m = getMinimumVar cnf_TopRemoved
             in case m of
                 Nothing -> do
                     --print inst
                     dpll_ (cnf_TopRemoved, inst, SAT)
                 Just x  -> let
                                cnf_Splitting = split_ x cnf_TopRemoved
                                ss'' = S.insert x $ getSingletons cnf_Splitting --このss''はinstに追加するためのものなのでmを加えておく。のちにUNSATが判明したら撤回。
                                inst'' = S.union ss'' inst -- 既存のInstanceにs''を合併
                                f'' = flagCheck cnf_Splitting -- cnf_Splittingが空集合ならばSAT、空集合を含めばUNSAT
                            in do
                                (c,i,f) <- dpll_ (cnf_Splitting,inst'',f'') -- 再帰は深さ優先探索的に行う
                                if f == UNSAT
                                then let 
                                       cnf_Splitting'' = split_ (-x) cnf_TopRemoved -- mでUNSATならば-mで試す。
                                       singletons'' = S.insert (-x) $ getSingletons cnf_Splitting''  -- mでUNSATになる場合はgetSingletonsも-mで作り直し。これもまたinstanceのためのもの
                                       instances''  = S.union singletons'' inst      -- instancesも同様。
                                     in do
                                         -- print instances''
                                         dpll_ (cnf_Splitting'',instances'',PARTIAL) -- flagは再び初期状態PARTIALに戻す
                                else return (c,i,f) -- このときf == SATである。（再帰が止まったあとなのでPARTIALではない）

dpll :: (Int,CNF,Instance,Flag) -> IO ()
dpll (n,cnf,inst,flag) = do
    (c,i,f) <- timeItNamed "DPLL" $ dpll_ (cnf,inst,flag)
    if f == UNSAT
        then print UNSAT
        else do
            print SAT
            let sn = S.fromList [1..n] -- simplify_の過程で消えた変数を補完する。消えた変数はTRUEでもFALSEでも構わないということなので標準的に1を代入する。
                iAbs = S.map abs i -- 消えた変数の補完に用いる
                iComp = S.difference sn iAbs -- 1,2,...,nのうち、iに現れない変数を差集合として導出
                i' = S.union i iComp -- 補完したInstance集合
                vs = sort $ S.toList i' -- Instancesをリスト化
                printVar n = putStrLn $ show (abs n) ++ ": " ++ show (signum n) -- Tは1、⊥は-1で表す
                printVars ns = sequence_ $ map printVar ns
            printVars vs

            
-- 以下はボツ関数

-- setSingletons (cnf,ss,ins) = 
--     let ss' = getSingletons cnf
--         cnf' = deleteSingleton cnf
--         res = insertSingleton ss' ss
--     in case res of
--         Nothing -> 
--         Right ss'' -> return (cnf',)

-- deleteSingleton :: CNF -> CNF
-- 回収したSingletonが既存のSingletonと矛盾しないかチェック
-- 矛盾する場合はFalse、しない場合はTrue。
-- isInconsistent :: Var -> Singletons -> Bool
-- isInconsistent v s = if S.member (-v) s 
--                 then False
--                 else True

-- deleteSingleton cnf = filter (not.isSingleton) cnf

-- 回収したSingletonの中に矛盾するペアがあったら知らせ、なければそれを次のSingletonとして返す関数。
-- insertSingleton :: Singletons -> Singletons -> Maybe Singletons
-- insertSingleton s1 s2 = 
--     if S.null s1 
--         then return s2 -- s1が空集合ならばs2を返す
--         else do
--             let x = S.findMin s1
--             if isConsistent x s2 
--                 then Nothing -- 矛盾が見つかれば検知
--                 else 
--                     let s1' = S.delete x s1
--                         s2' = S.insert x s2 
--                     in insertSingleton s1' s2' -- 見つからなければs1'のサイズを減らして再帰。第二引数が蓄積引数。