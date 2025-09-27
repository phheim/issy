module Issy.Utils.Concurrent(parallelStrictFirst) where

import Control.Concurrent(forkIO, killThread)
import Control.Concurrent.MVar(MVar, readMVar, putMVar, newEmptyMVar)


parallelStrictFirst :: [a] -> IO a
parallelStrictFirst xs 
    | null xs = error "assert: should not be null"
    | otherwise = do
        mvar <- newEmptyMVar
        workers <- mapM (forkIO . worker mvar) xs
        res <- readMVar mvar
        _ <- mapM killThread workers
        pure res
    where
        worker :: MVar a -> a -> IO ()
        worker resMVar value = (do pure $! value) >>= putMVar resMVar

