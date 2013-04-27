{-# LANGUAGE
  TupleSections
  #-}
module Interpreter where

import Prelude hiding (mapM)

import Control.Applicative
import Data.Foldable
import qualified Data.Map as M
import Data.Monoid
import Data.Traversable
import GHC.Int
import System.IO.Unsafe

{- 
 - This is an interpreter for a pure, lazy, dynamically typed, functional
 - language. It implements objects (labelled product types),
 - switchables (labelled sum types), switch statements (a very limited
 - form of pattern matching), let statements, let-switchtags, lists, maybes, and
 - even monadic return and bind for the write and IO monad, and it's just over 400
 - lines.
 -
 - Some of the ADTs have lots and lots of constructors. This approach
 - is not extensible (when you don't have access to the source code),
 - it is not concise, and the monadic actions are currently restricted to IO.
 - 
 - The only advantage of this approach is that it is very easy to follow.
 -
 - The main challenge of writing a lazy interpreter is sharing structure: in
 - particular, making sure that an individual closure is not evaluated more
 - than once. Obvious but tedious solutions include using IORefs and monadic
 - state. This interpreter uses a completely different tactic: exploiting
 - unsafeInterleaveIO. All function arguments are evaluated "right away", but in the
 - context of an unsafeInterleaveIO (so, in fact, they are actually not evaluated
 - right away). With this hack, we get to write an interpreter which LOOKS
 - like an interpreter for a strict functional language, but actually
 - behaves lazily (by lifting haskell's own lazy semantics into our interpreter).
 -
 - Primitives are duplicated into two types: Literal and Value. This is redundant,
 - but it makes the interpreter very simple. Making the input and output of 'eval'
 - be different types makes certain kinds of bugs impossible. For example,
 - having a very clear point at which literals turn into values ensures
 - that side-effects happen at the right time. See, for example, the code
 - involving 'LPrintHelloWorld'.
 -}

-- The Exp data type is extremely simple. Notice that there is no way to get a Value
-- into Exp. You could sneak it in by adding a Value to one of the constructors on
-- Literal, but this is a bad idea. Exp is supposed to be limited to the original
-- source text of the program. You should never need to generate an Exp.
data Exp = App Exp Exp | Var String | Literal Literal
  deriving (Show)

-- Literal is anything that can be PARSED from a program but which does not appear
-- in the Exp data type above. This includes language constructs (like let and switch),
-- primitives (like ints and reals), and primitive functions (like foldList).
-- You shouldn't need to do anything clever here... notice, for instance, that
-- LSwitchStatement has exactly the components you would expect it to: the determinent
-- expression, and a map from switchtags to parameters and expression. An alternative
-- approach would be to embed lambdas inside each of the branches of a switch,
-- but that would complicates things unnecessarily.
--
-- Most constructors in Literal have multiple corresponding constructors in Value.
-- For example, LFoldList has corresponding constructors VFoldList, VFoldList1, and
-- VFoldList2. I have chosen to make each partial applicative of the literals it's own
-- constructor. This makes the code slightly longer but it is also magnitudes easier
-- to understand. We also get the benifit of GHC warning us when we have forgotten
-- to pattern match against a case (when warnings are turned on).
--
-- Although most constructors in Literal have corresponding constructors in Value, not
-- all of them do. For instance, LLet jumps straight into reducing itself when you
-- call literalToValue.
--
-- If you combine a Literal with an Env, you get a Value out. That is what
-- literalToValue does. As you add constructors to Literal, you will need to extend
-- literalToValue.
data Literal =
    -- The beloved lambda:
    LLam String Exp

    -- Let. Recursive bindings is currently broken; see the comment in literalToValue.
  | LLet (M.Map String Exp) Exp

    -- Let-switch brings constructors into scope.
    --
    -- e.g.
    -- (let { switchers { nothing; just } } (just 7).
    --
    -- Since the language is dynamically typed, and there is no way
    -- to define ADTs, we need a way of telling the interpreter that
    -- 'just' is a constructor.
    -- Without this construct, we would get an 'unbound variable' error.
  | LLetSwitchTags [String] Exp

    -- Ints couldn't be any simpler.
  | LInt Int64
  | LReal Double

    -- Add is overloaded to work with both ints and reals. (See VAdd1 in applyValue.)
    -- You will need to add overloads for many other data types as well.
  | LAdd

    -- Objects! Recursive bindings are also broken here; see the comment in literalToValue.
  | LObject (M.Map String Exp)
  | LObjectDereference String

  | LSwitchStatement
      Exp
      (M.Map
        String {- constructor -}
        (Maybe String {- param; Nothing means wildcard -}, Exp))

  -- Nothing and Just. Constructors for the Maybe type.
  | LNull
  | LJust
  | LFoldMaybe -- b -> (a -> b) -> Maybe a -> b

  -- Literal lists. In literalToValue, this is converted into a bunch of applications
  -- of VCons2.
  | LList [Exp]

  -- The cons function. (a -> [a] -> [a])
  | LCons

  -- The empty list.
  | LNil

  | LFoldList
  | LUnfoldList -- (b -> Maybe (a, b)) -> b -> [a] -- The (a,b) tuple is actually an object with properties _1 and _2.

  -- monadic operations:
  | LOnly -- aka as "return" in haskell... calling it "only" matches the fmap/join understanding of monads better
  | LBind -- m a -> (a -> m b) -> m b

  -- just a goofy function to demonstrate that IO works
  | LPrintHelloWorld -- IO ()
  deriving (Show)

-- Values exist only at runtime. These are kept in the Env.
--
-- With the exception of VLam, NONE of these constructors make a reference back
-- to Exp. What's that you say? How can these data structures possibly be lazy
-- if they don't make a reference back to Exp? I'm glad you asked! The explanation
-- is coming up soon, but it basically boils down to one magic word:
--   unsafeInterleaveIO.
--
-- The behavior of these values is defined in applyValue.
data Value =
    -- The only constructor that refers back to Exp. Most toy interpreters
    -- call this a Closure.
    VLam Env String Exp

    -- obviously ints exist both at parse time and at run time, so we need a
    -- constructor for them in both Literal and Value.
  | VInt Int64
  | VReal Double
    
    -- the primitive add function
  | VAdd
  
    -- the primitive add function partially applied to one of its arguments
    -- There is no need for a VAdd2, because at that point you reduce back down
    -- to VInt or VReal.
  | VAdd1 Value

    -- Objects at runtime instead of at parse time. Notice the elems of the map are
    -- values, not expressions.
  | VObject (M.Map String Value)
  | VObjectDereference String

    -- This does not have a corresponding form in 'Literal'. It is instead
    -- created by use of 'LLetSwitchTags'
  | VSwitchableConstructor String
    -- apply a VSwitchableConstructor to a value and you get
    -- a constructed switchable!
  | VConstructedSwitchable String Value

  | VNil

    -- Add and Cons both take two arguments. However, Add stops after only one partial
    -- application, because after that it reduces. Cons continues up to the second
    -- partial application, because it is a constructor.
  | VCons
  | VCons1 Value
  | VCons2 Value Value

  | VNull
  | VJust
  | VJust1 Value

  | VFoldMaybe
  | VFoldMaybe1 Value
  | VFoldMaybe2 Value Value

  | VFoldList
  | VFoldList1 Value
  | VFoldList2 Value Value
  | VUnfoldList
  | VUnfoldList1 Value

    -- "return" in haskell. Produces a VAction when applied to something.
  | VOnly

    -- the container for values in the io monad
  | VAction Action

    -- applying Bind1 to a value will cause the effect of the monad to occur
  | VBind
  | VBind1 Value
  deriving (Show)

data Action = Action String (IO Value)

instance Show Action where
  show (Action s _) = s

-- Env just maps from strings (variable names) to values. No IORefs in sight.
newtype Env = Env (M.Map String Value)
  deriving (Show)

-- And now the magic.
eval :: (Env, Exp) -> IO Value
eval (env@(Env bindings),exp) = do
  case exp of
    App e1 e2 -> do
      val <- eval (env,e1)
      arg <- unsafeInterleaveIO $ eval (env, e2) -- <-- magic is right here!
      applyValue val arg
    Var s ->
      case M.lookup s bindings of
        Nothing -> error $ "unbound variable: " ++ s
        Just val -> return val
    Literal lit -> literalToValue env lit

literalToValue :: Env -> Literal -> IO Value
literalToValue env@(Env bindings) lit =
  case lit of
    LLam s e -> return (VLam env s e)
    LLet mp e -> do
      newMp <- mapM (unsafeInterleaveIO . eval . (env,) {- <-- todo: make recursive -}) mp
      eval ((Env $ M.union newMp bindings),e)
    LLetSwitchTags tags e ->
      eval ((Env $ M.union switchtags bindings), e) where
        switchtags = M.fromList (map (\t -> (t, VSwitchableConstructor t)) tags)
    LInt i -> return (VInt i)
    LReal r -> return (VReal r)
    LAdd -> return VAdd
    LObject mp -> do
      -- todo: allow objects to be recursive.
      -- The current env should be unioned with
      -- the environment with the object itself (definitions within the object should
      -- shadow definitions outside the object). To get this working properly, GHC's DoRec
      -- extension will be helpful.
      newMp <- mapM (unsafeInterleaveIO . eval . (env,) {- <-- incomplete -}) mp
      return (VObject newMp)
    LObjectDereference field -> return (VObjectDereference field)
    LSwitchStatement det branches -> do
      VConstructedSwitchable str clos <- eval (env,det)
      case M.lookup str branches of
        Nothing -> error "no branch in switch exists for that tag"
        Just (Nothing, body) -> eval (env,body)
        Just (Just param, body) -> eval ((Env $ M.insert param clos bindings),body)
    LList exps -> foldrM (\hd tl -> VCons2 <$> unsafeInterleaveIO (eval (env,hd)) <*> pure tl) VNil exps
    LCons -> return VCons
    LNil -> return VNil
    LNull -> return VNull
    LJust -> return VJust
    LFoldMaybe -> return VFoldMaybe
    LFoldList -> return VFoldList
    LUnfoldList -> return VUnfoldList
    LOnly -> return VOnly
    LBind -> return VBind
    LPrintHelloWorld -> return (VAction (Action "print-hello-world" (putStrLn "Hello, world!" >> return unitObject))) -- side effect occurs in VBind1, not here.

applyValue :: Value -> Value -> IO Value
applyValue val arg =
  case val of
    VLam (Env e) s body -> eval ((Env $ M.insert s arg e), body)
    VInt _ -> error "cannot apply a integral number to something else"
    VReal _ -> error "cannot apply a floating point number to something else"
    VAdd -> return (VAdd1 arg) -- hold on to partially applied argument
    VAdd1 lhs ->
      case (lhs, arg) of
        -- if you wanted type coercion, it would go here
        (VInt i, VInt j) -> return (VInt (i + j))
        (VReal i, VReal j) -> return (VReal (i + j))
        _ -> error "type mismatch: add expected integers"

    VObject _ -> error "object cannot be applied to something else"
    VObjectDereference prop ->
      case arg of
        VObject objMap ->
          case M.lookup prop objMap of
            Nothing -> error "object does not have that property"
            Just val -> return val
        _ -> error "type mismatch; dereferenced a non-object"

    -- LSwitchStatement in literalToValue shows how VConstructedSwitchable gets used
    VSwitchableConstructor str -> return $ VConstructedSwitchable str arg
    VConstructedSwitchable _ _ -> error "a switchable cannot be applied to anything"

    VNil -> error "nil cannot be applied"
    VCons -> return $ VCons1 arg
    VCons1 hd -> return $ VCons2 hd arg
    VCons2 _ _ -> error "a list cannot be applied"

    VNull -> error "null cannot be applied"
    VJust -> return $ VJust1 arg
    VJust1 _ -> error "just has already been applied; cannot be applied again"

    VFoldMaybe -> return $ VFoldMaybe1 arg
    VFoldMaybe1 x -> return $ VFoldMaybe2 x arg
    VFoldMaybe2 x y ->
      case arg of
        VNull -> return x
        VJust1 z -> applyValue y z
        _ -> error "type mismatch: not a maybe"

    VFoldList -> return $ VFoldList1 arg
    VFoldList1 x -> return $ VFoldList2 x arg
    VFoldList2 x y ->
      case arg of
        VNil -> return y
        VCons2 hd tl -> do
          partial <- applyValue x y
          newSeed <- applyValue partial hd
          applyValue (VFoldList2 x newSeed) tl
        _ -> error "type mismatch; foldList on a non-list"
    VUnfoldList -> return $ VUnfoldList1 arg
    VUnfoldList1 x -> do
      mb <- applyValue x arg
      case mb of
        VNull -> return VNil
        VJust1 (VObject mp) ->
          case (M.lookup "_1" mp, M.lookup "_2" mp) of
            (Just nextVal, Just nextSeed) -> do
              tl <- unsafeInterleaveIO $ applyValue (VUnfoldList1 x) nextSeed
              return $ VCons2 nextVal tl
            _ -> error "unfoldList expected an object with properties _1 and _2, but didn't find them"
        _ -> error "type mismatch; first arg of unfoldList is supposed to produce a maybe 2-tuple (2-tuple is an object with properties _1 and _2)"

    VOnly -> return $ VAction (Action "only" (return arg))
    VAction _ -> error "io and write actions cannot be applied; use bind to see their effects"

    VBind -> return $ VBind1 arg
    -- here is where io action effects actually occur
    VBind1 x ->
      case x of
        VAction (Action _ act) -> do
          out <- act -- side effect!
          applyValue arg out
        _ -> error "type mismatch; first arg of bind is not an action"

unitObject = VObject mempty
