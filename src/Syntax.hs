module Syntax where

data LambdaPlus
	= LPVar String
	| LPApp LambdaPlus LambdaPlus
	| LPLam String LambdaPlus
	| LPLet String LambdaPlus LambdaPlus
	| LPFix String LambdaPlus

	| LPCons LambdaPlus LambdaPlus
	| LPNil
	| LPInt Int

	| LPMonitor Contract LambdaPlus


data Value
	= VInt Int
	| VCons Value Value
	| VNil
	| VLam String LambdaPlus


data Contract
	= CTrue
	| CFalse
	| CRef String LambdaPlus
	| CFunc String Contract Contract


-- * Evaluation

type Env = [(String, Value)]

data MonitorResult
	= MFail String
	| MSuccess

instance Monoid MonitorResult where
	m@(MFail _) `mappend` _ = m
	_ `mappend` x = x
	mzero = MSuccess

newtype Eval env a = Eval (ExceptT String (RWST Env [MonitorResult] () (Identity a)))
	deriving (Monad, MonadWriter, MonadReader, MonadExcept)

getVar :: String -> Eval Value
getVar x = do
	mbVal <- lookup x <$> get
	case mbVal of
		Nothing -> throw ("Unbound variable: " <> x)
		Just v -> return v

withEnv :: Env -> Eval Value -> Eval Value
withEnv = local

recordViolation :: MonitorResult -> Eval ()
recordViolation = write

eval :: LambdaPlus -> Eval Value
eval t = do
	env <- get
	case t of
		LPVar x -> 
			getVar x
		LPApp t1 t2 -> do
			Lam x t <- eval t1
			v 		<- eval t2
			withEnv ((x,v):env) (eval t)				
		LPLam x t ->
			VLam x t
		LPLet x t1 t2 -> do
			v <- eval t1
			withEnv ((x,v:env) (eval t2))
		LPFix x t ->
			undefined
		LPCons h t -> 
			VCons <$> eval h <*> eval t
		LPNil -> 
			VNil
		LPInt x ->
			VInt x
		LPMonitor CTrue t ->
			eval t
		LPMonitor CFalse t -> do
			recordViolation "False contract occurred"
			eval t
		LPMonitor c@(CRefinement var ref) t -> do
			res <- withEnv ((var, v):env) (evalRefinement ref)
			when (res == VFalse) $ do
				recordViolation (show t <> " does not satisfy " <> show c)
			eval t
		LPMonitor c@(CFunction x c1 c2) t = do
			eval (LPFunc x 
					 (LPLet "_v" (LPMonitor c1) 
	 			         (LPMonitor c2
	 			         	 (LPApp t (LPVar "_v")))))


evalRefinement :: LambdaPlus -> Eval Value
evalRefinement t = do
	eval t


eval :: Env -> LambdaPlus -> Value
eval env term = 
	case term of
		LPVar x -> fromMaybe (error "Not in scope: " <> x) (lookup x env)
		LPApp t1 t2 -> let VLam x t = eval env t1 
						   arg      = eval env t2
					   in eval ((x, arg):env) t
		LPLam x t -> VLam x t
		LPLet x t1 t2 -> let val = eval env t1 in eval ((x, val):
