package freeboogie.tc;

//{{{ imports
import java.math.BigInteger;
import java.util.*;

import com.google.common.base.Supplier;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Maps;
import com.google.common.collect.UnmodifiableIterator;
import genericutils.*;

import freeboogie.ast.*;

import static freeboogie.cli.FbCliOptionsInterface.*;
//}}}

/**
  Typechecks an AST.

  It also acts more-or-less as a Facade for the whole package.

  The typechecking works as follows. The {@code eval}
  functions associate types to nodes in the AST that represent
  expressions. The {@code check} functions verify equality modulo
  substitutions for type variables. Comparing types is done
  structurally.

  Type checking assumes that type synonyms were desugared.

  @author rgrig
 */
public class TypeChecker extends Evaluator<Type> implements TcInterface {
  // BEGIN data memebers {{{
  // shorthand notations
  private static final BigInteger ZERO = BigInteger.valueOf(0);
  private static final BigInteger MAX_INT =
      BigInteger.valueOf(Integer.MAX_VALUE);

  private static final Logger<LogCategories, LogLevel> log =
      Logger.<LogCategories, LogLevel>get("log");

  // used for primitive types (so reference equality is used below)
  private static final PrimitiveType boolType =
      PrimitiveType.mk(PrimitiveType.Ptype.BOOL, -1, FileLocation.unknown());
  private static final PrimitiveType intType =
      PrimitiveType.mk(PrimitiveType.Ptype.INT, -1, FileLocation.unknown());

  // used to signal an error in a subexpression and to limit
  // errors caused by other errors
  private static final PrimitiveType errType =
      PrimitiveType.mk(PrimitiveType.Ptype.ERROR, -1, FileLocation.unknown());

  private SymbolTable st;
  private GlobalsCollector gc;
  private FlowGraphMaker flowGraphs;

  // detected errors
  private List<FbError> errors;

  // maps implementations to procedures
  private UsageToDefMap<Implementation, Procedure> implProc;

  // maps implementation params to procedure params
  private UsageToDefMap<VariableDecl, VariableDecl> paramMap;

  // used for (randomized) union-find
  private static final Random rand = new Random(0);

  // implicitSpec.get(x) contains the mappings of type variables
  // to types that were inferred (and used) while type-checking x
  private Map<Ast, Map<Identifier, Type>> implicitSpec;

  // used as a stack of sets; this must be updated whenever
  // we decend into something parametrized by a generic type
  // that can contain expressions (e.g., functions, axioms,
  // procedure, implementation, quantifiers)
  private StackedHashMap<Identifier, Identifier> enclosingTypeVar;
  private boolean ignoreEnclosingTypeVariables;  // used for checking ==

  // maps type variables to their binding types
  private StackedHashMap<Identifier, Type> typeVar;

  // records the last processed AST
  private Program ast;

  private int tvLevel; // DBG
  /// END data members }}}

  // BEGIN public interface {{{
  /**
   * Returns implicit specializations deduced/used by the typechecker
   * at various points in the AST. If later you want to check the
   * specialization performed for an ID then you should find the
   * mappings of type variables stored for ALL parents of the ID.
   */
  public Map<Ast, Map<Identifier, Type>> implicitSpec() {
    return implicitSpec;
  }

  @Override
  public Program process(Program ast) throws ErrorsFoundException {
    assert new TreeChecker().isTree(ast) : "AST is a dag instead of a tree";

    tvLevel = 0; // DBG

    typeVar = new StackedHashMap<Identifier, Type>();
    enclosingTypeVar = new StackedHashMap<Identifier, Identifier>();
    implicitSpec = Maps.newHashMap();

    // build symbol table
    SymbolTableBuilder stb = new SymbolTableBuilder();
    ast = stb.process(ast, null);
    st = stb.st();
    gc = stb.gc();

    // check implementations
    ImplementationChecker ic = new ImplementationChecker();
    errors = ic.process(ast, gc);
    if (!errors.isEmpty()) throw new ErrorsFoundException(errors);
    implProc = ic.implProc();
    paramMap = ic.paramMap();

    // check blocks
    flowGraphs = new FlowGraphMaker();
    flowGraphs.process(ast);

    // do the typecheck
    AstUtils.evalListOfAxiom(ast.axioms(), this);
    AstUtils.evalListOfVariableDecl(ast.variables(), this); // for 'where'
    AstUtils.evalListOfConstDecl(ast.constants(), this);  // for 'where'
    AstUtils.evalListOfProcedure(ast.procedures(), this);
    AstUtils.evalListOfImplementation(ast.implementations(), this);

    if (!errors.isEmpty()) throw new ErrorsFoundException(errors);

    return ast;
  }

  @Override
  public SimpleGraph<Command> flowGraph(Implementation implementation) {
    SimpleGraph<Command> result = flowGraphs.flowGraph(implementation);
    assert result != null : "You must compute flowgraphs first.";
    return result;
  }

  public LabelsCollector labels() {
    return flowGraphs.labels();
  }

  /* The cast is ugly, I know, but it reduces significantly memory use.
    The good FIX is to have persistent data structures recording the
    extra information associated with AST nodes, and it will take some
    time to implement. */
  @SuppressWarnings("unchecked")
  @Override
  public Map<Expr, Type> types() {
    return (Map<Expr, Type>)(Object)Collections.unmodifiableMap(evalCache);
  }

  @Override
  public UsageToDefMap<Implementation, Procedure> implProc() {
    return implProc;
  }

  @Override
  public UsageToDefMap<VariableDecl, VariableDecl> paramMap() {
    return paramMap;
  }

  @Override
  public SymbolTable st() {
    return st;
  }
  // END public interface }}}

  // BEGIN helper methods {{{
  private static void info(String s) {
    log.say(LogCategories.TYPECHECK, LogLevel.INFO, s);
  }

  private static void info(Supplier<String> s) {
    log.say(LogCategories.TYPECHECK, LogLevel.INFO, s);
  }

  // |ast| may be used for debugging
  private void typeVarEnter(Ast ast) {
    typeVar.push();
    ++tvLevel;
  }

  private void typeVarExit(Ast ast) {
    Map<Identifier, Type> lis = Maps.newHashMap();
    implicitSpec.put(ast, lis);
    for (Map.Entry<Identifier, Type> e : typeVar.peek().entrySet())
      if (!isTypeVar(e.getValue())) lis.put(e.getKey(), e.getValue());
    typeVar.pop();
    --tvLevel;
  }

  // gives a TupleType with the types in that list
  private TupleType typeListOfDecl(ImmutableList<VariableDecl> l) {
    ImmutableList.Builder<Type> builder = ImmutableList.builder();
    for (VariableDecl vd : l) builder.add(vd.type());
    return TupleType.mk(builder.build());
  }

  // Computes a TupleType for a list of expressions
  private TupleType typeListOfExpr(ImmutableList<? extends Expr> es) {
    ImmutableList.Builder<Type> builder = ImmutableList.builder();
    for (Expr e : es) builder.add(e.eval(this));
    return TupleType.mk(builder.build());
  }

  private boolean eq(PrimitiveType a, PrimitiveType b) {
    return a.ptype() == b.ptype();
  }

  private boolean eq(MapType a, MapType b) {
    if (!eq(b.idxTypes(), a.idxTypes())) return false;  // contravariant
    return eq(a.elemType(), b.elemType()); // covariant
  }

  private boolean eq(UserType a, UserType b) {
    return a.name().equals(b.name()) && eq(a.typeArgs(), b.typeArgs());
  }

  private boolean eq(ImmutableList<Type> a, ImmutableList<Type> b) {
    if (a.size() != b.size()) return false;
    UnmodifiableIterator<Type> ia = a.iterator();
    UnmodifiableIterator<Type> ib = b.iterator();
    while (ia.hasNext()) if (!eq(ia.next(), ib.next())) return false;
    return true;
  }

  private boolean eq(TupleType a, TupleType b) {
    return eq(a.types(), b.types());
  }

  /* Checks whether |a| and |b| represent the same type. */
  private boolean eq(Type a, Type b) {
    if (a == b) return true; // the common case
    if (a == errType || b == errType) return true; // don't bubble up errors

    // (t) == t
    a = stripTuple(a);
    b = stripTuple(b);

    // handle type variables
    a = realType(a);
    b = realType(b);
    if (isTypeVar(a) || isTypeVar(b)) {
      equalTypeVar(a, b);
      return true;
    }

    // the main check
    if (a instanceof PrimitiveType && b instanceof PrimitiveType)
      return eq((PrimitiveType)a, (PrimitiveType)b);
    else if (a instanceof MapType && b instanceof MapType)
      return eq((MapType)a, (MapType)b);
    else if (a instanceof UserType && b instanceof UserType)
      return eq((UserType)a, (UserType)b);
    else if (a instanceof TupleType && b instanceof TupleType)
      return eq((TupleType) a, (TupleType) b);
    else
      return false;
  }

  /* Checks whether |a| and |b| may represent the same type by substituting
    (some) real types for the type variables they contain. */
  private boolean possiblyEq(Type a, Type b) {
    assert !ignoreEnclosingTypeVariables : "no nesting";
    ignoreEnclosingTypeVariables = true;
    boolean r = eq(a, b);
    ignoreEnclosingTypeVariables = false;
    return r;
  }

  private Type stripTuple(Type t) {
    if (!(t instanceof TupleType)) return t;
    TupleType tt = (TupleType) t;
    if (tt.types().size() != 1) return t;
    return stripTuple(tt.types().get(0));
  }

  private void collectEnclosingTypeVars(ImmutableList<Identifier> ids) {
    for (Identifier i : ids) enclosingTypeVar.put(i, i);
  }

  private Type realType(Type t) {
    Identifier ai;
    Type nt;
    while (true) {
      ai = getTypeVarDecl(t);
      if (ai == null || (nt = typeVar.get(ai)) == null) break;
      typeVar.put(ai, nt);
      t = nt;
    }
    return t;
  }

  /* Substitutes real types for (known) type variables.
   * If the result is a type variable then an error is reported
   * at location {@code loc}. */
  private Type checkRealType(Type t, Ast l) {
    t = substRealType(t);
    if (isTypeVar(t)) {
      errors.add(new FbError(FbError.Type.REQ_SPECIALIZATION, l,
            TypeUtils.typeToString(t), t.loc(), getTypeVarDecl(t)));
      t = errType;
    }
    return t;
  }

  private ImmutableList<Type> checkRealType(ImmutableList<Type> ts, Ast l) {
    ImmutableList.Builder<Type> builder = ImmutableList.builder();
    for (Type t : ts) builder.add(checkRealType(t, t));
    return builder.build();
  }

  /* Changes all occurring type variables in {@code t} into
   * the corresponding real types.  */
  private Type substRealType(Type t) {
    if (t == null) return null;
    if (t instanceof TupleType) {
      TupleType tt = (TupleType) t;
      return TupleType.mk(substRealType(tt.types()), t.loc());
    } if (t instanceof MapType) {
      MapType at = (MapType)t;
      return MapType.mk(
          at.typeVars(),
          substRealType(at.idxTypes()),
          substRealType(at.elemType()));
    }
    Type nt = realType(t);
    return nt;
  }

  private ImmutableList<Type> substRealType(ImmutableList<Type> ts) {
    ImmutableList.Builder<Type> builder = ImmutableList.builder();
    for (Type t : ts) builder.add(substRealType(t));
    return builder.build();
  }

  private boolean isTypeVar(Type t) {
    Identifier ai = getTypeVarDecl(t);
    return ai != null &&
        (ignoreEnclosingTypeVariables || enclosingTypeVar.get(ai) == null);
  }

  private Identifier getTypeVarDecl(Type t) {
    if (!(t instanceof UserType)) return null;
    return st.typeVars.def((UserType)t);
  }

  // pre: |a| and |b| are as 'real' as possible
  private void equalTypeVar(Type a, Type b) {
    assert !isTypeVar(a) || !typeVar.containsKey(getTypeVarDecl(a));
    assert !isTypeVar(b) || !typeVar.containsKey(getTypeVarDecl(b));
    if (!isTypeVar(a) && !isTypeVar(b)) {
      assert TypeUtils.eq(a, b);
      return;
    }
    if (!isTypeVar(a) || (isTypeVar(b)  && rand.nextBoolean())) {
      Type t = a; a = b; b = t;
    }
    final Identifier ai = getTypeVarDecl(a);
    final Type bb = b;
    if (getTypeVarDecl(b) != ai) {
      info(new Supplier<String>() {
        @Override public String get() {
          return "" + ai.id() + "@" + ai.loc() + "==" +
              TypeUtils.typeToString(bb); // this one takes time
        }
      });
      assert tvLevel > 0 :
          "you probably need to add typeVarEnter/Exit in some places";
      typeVar.put(ai, b);
    }
  }

  private void mapExplicitGenerics(
      ImmutableList<Identifier> tvl,
      ImmutableList<Type> tl
  ) {
    if (tvl.size() < tl.size()) {
      errors.add(new FbError(FbError.Type.GEN_TOOMANY, tl.get(tvl.size())));
      return;
    }
    assert tvLevel > 0;
    UnmodifiableIterator<Identifier> itv = tvl.iterator();
    UnmodifiableIterator<Type> it = tl.iterator();
    while (it.hasNext()) typeVar.put(itv.next(), it.next());
  }

  /**
   * If {@code a} cannot be used where {@code b} is expected then an error
   * at location {@code l} is produced and {@code errors} is set.
   */
  private void check(Type a, Type b, Ast l) {
    if (eq(a, b)) return;
    errors.add(new FbError(FbError.Type.BAD_TYPE, l,
          TypeUtils.typeToString(a), TypeUtils.typeToString(b)));
  }

  /** Checks that two types may be equal. */
  private void checkLenient(Type a, Type b, Ast l) {
    if (possiblyEq(a, b)) return;
    errors.add(new FbError(FbError.Type.BAD_TYPE, l,
          TypeUtils.typeToString(a), TypeUtils.typeToString(b)));
  }

  // Check whether |t| is a bit vector.
  private BigInteger checkBv(Type t, Ast l) {
    if (t instanceof PrimitiveType) {
      PrimitiveType pt = (PrimitiveType) t;
      if (pt.ptype() == PrimitiveType.Ptype.INT && pt.bits() >= 0)
        return BigInteger.valueOf(pt.bits());
    }
    errors.add(new FbError(FbError.Type.BV_REQUIRED, l));
    return BigInteger.valueOf(-1);
  }

  private void checkLe(BigInteger a, BigInteger b, Ast l) {
    if (a.compareTo(b) <= 0) return;
    errors.add(new FbError(FbError.Type.LE, l, a, b));
  }

  private PrimitiveType bvt(int w) {
    return PrimitiveType.mk(PrimitiveType.Ptype.INT, w);
  }

  private PrimitiveType bvt(BigInteger w) {
    return bvt(w.intValue());
  }
  // END helper methods }}}

  // BEGIN visiting operators {{{
  @Override public Type eval(UnaryOp unaryOp) {
    Expr expr = unaryOp.expr();
    Type t = expr.eval(this);
    switch (unaryOp.op()) {
    case MINUS:
      check(t, intType, expr);
      return memo(unaryOp, intType);
    case NOT:
      check(t, boolType, expr);
      return memo(unaryOp, boolType);
    default:
      assert false;
      return null;
    }
  }

  @Override public Type eval(BinaryOp binaryOp) {
    Expr left = binaryOp.left();
    Expr right = binaryOp.right();
    Type l = left.eval(this);
    Type r = right.eval(this);
    switch (binaryOp.op()) {
    case CONCAT:
      BigInteger w1 = checkBv(l, left);
      BigInteger w2 = checkBv(r, right);
      if (w1.signum() == -1 || w2.signum() == -1)
        return memo(binaryOp, errType);
      w1 = w1.add(w2);
      if (w1.compareTo(MAX_INT) > 0) {
        errors.add(new FbError(FbError.Type.TOO_FAT, binaryOp, w1));
        return memo(binaryOp, errType);
      }
      return memo(binaryOp, bvt(w1));
    case PLUS:
    case MINUS:
    case MUL:
    case DIV:
    case MOD:
      // integer arguments and integer result
      check(l, intType, left);
      check(r, intType, right);
      return memo(binaryOp, intType);
    case LT:
    case LE:
    case GE:
    case GT:
      // integer arguments and boolean result
      check(l, intType, left);
      check(r, intType, right);
      return memo(binaryOp, boolType);
    case EQUIV:
    case IMPLIES:
    case AND:
    case OR:
      // boolean arguments and boolean result
      check(l, boolType, left);
      check(r, boolType, right);
      return memo(binaryOp, boolType);
    case SUBTYPE:
      // l subtype of r and boolean result (TODO: a user type is a subtype of a user type)
      check(l, r, left);
      return memo(binaryOp, boolType);
    case EQ:
    case NEQ:
      // typeOf(l) == typeOf(r) and boolean result
      typeVarEnter(binaryOp);
      checkLenient(l, r, binaryOp);
      typeVarExit(binaryOp);
      return memo(binaryOp, boolType);
    default:
      assert false : "Unknown oprator " + binaryOp.op().name();
      return errType; // dumb compiler
    }
  }
  // END visiting operators }}}

  // BEGIN visiting expressions {{{
  @Override public Type eval(Cast cast) {
    cast.expr().eval(this);
    return memo(cast, cast.type());
  }

  @Override public Type eval(Identifier id) {
    IdDecl d = st.ids.def(id);
    Type t = errType;
    if (d instanceof VariableDecl) {
      VariableDecl vd = (VariableDecl)d;
      typeVarEnter(id);
      mapExplicitGenerics(vd.typeArgs(), id.types());
      t = checkRealType(vd.type(), id);
      typeVarExit(id);
    } else if (d instanceof ConstDecl) {
      t = ((ConstDecl)d).type();
    } else {
      assert false :
          "SymbolTableBuilder didn't do its job properly: " +
          id.id() + "(" + id.loc() + ")";
    }
    assert t != null;
    return memo(id, t);
  }

  @Override public Type eval(Slice slice) {
    Type bvt = slice.bv().eval(this);
    BigInteger w = checkBv(bvt, slice.bv());
    if (w.signum() == -1) return memo(slice, errType);
    BigInteger low = slice.low().value().value();
    BigInteger high = slice.high().value().value();
    checkLe(ZERO, low, slice.low());
    checkLe(low, high, slice);
    checkLe(high, w, slice.high());
    return memo(slice, bvt(high.subtract(low)));
  }

  @Override public Type eval(NumberLiteral num) {
    if (num.value().width() < 0) return memo(num, intType);
    return memo(num, bvt(num.value().width()));
  }

  @Override public Type eval(BooleanLiteral atomLit) {
    switch (atomLit.val()) {
    case TRUE:
    case FALSE:
      return memo(atomLit, boolType);
    default:
      assert false;
      return errType; // dumb compiler
    }
  }

  @Override public Type eval(OldExpr atomOld) {
    return memo(atomOld, atomOld.expr().eval(this));
  }

  @Override public Type eval(Quantifier atomQuant) {
    Expr e = atomQuant.expression();
    enclosingTypeVar.push();
    collectEnclosingTypeVars(atomQuant.typeVariables());
    Type t = atomQuant.expression().eval(this);
    check(t, boolType, e);
    enclosingTypeVar.pop();
    return memo(atomQuant, boolType);
  }

  @Override public Type eval(FunctionApp atomFun) {
    FunctionDecl d = st.funcs.def(atomFun);
    Signature sig = d.sig();
    ImmutableList<VariableDecl> fargs = sig.args();

    typeVarEnter(atomFun);
    mapExplicitGenerics(sig.typeArgs(), atomFun.types());
    Type at = typeListOfExpr(atomFun.args());
    Type fat = typeListOfDecl(fargs);

    check(at, fat, atomFun);
    Type rt = checkRealType(typeListOfDecl(sig.results()), atomFun);
    typeVarExit(atomFun);
    return memo(atomFun, rt);
  }

  @Override public Type eval(MapSelect atomMapSelect) {
    Expr atom = atomMapSelect.map();
    Type t = atom.eval(this);
    if (t == errType) return memo(atomMapSelect, errType);
    if (!(t instanceof MapType)) {
      errors.add(new FbError(FbError.Type.NEED_ARRAY, atom));
      return memo(atomMapSelect, errType);
    }
    MapType at = (MapType)t;

    // look at indexing types
    ImmutableList<Expr> index = atomMapSelect.idx();
    typeVarEnter(atomMapSelect);
    TupleType ait = typeListOfExpr(index);
    TupleType fit = TupleType.mk(at.idxTypes());
    check(ait, fit, atomMapSelect);
    Type et = checkRealType(at.elemType(), atomMapSelect);
    typeVarExit(atomMapSelect);
    return memo(atomMapSelect, et);
  }

  @Override public Type eval(MapUpdate atomMapUpdate) {
    typeVarEnter(atomMapUpdate);
    Expr atom = atomMapUpdate.map();
    ImmutableList<Expr> index = atomMapUpdate.idx();
    Expr val = atomMapUpdate.val();
    Type t = atom.eval(this);
    Type ti = typeListOfExpr(index);
    Type tv = val.eval(this);
    if (
        TypeUtils.eq(t, errType) ||
        TypeUtils.eq(ti, errType) ||
        TypeUtils.eq(tv, errType)) return memo(atomMapUpdate, errType);
    MapType mt;
    if (!(t instanceof MapType)) {
      errors.add(new FbError(FbError.Type.NEED_ARRAY, atom));
      typeVarExit(atomMapUpdate);
      return memo(atomMapUpdate, errType);
    }
    mt = (MapType)t;
    check(typeListOfExpr(index), TupleType.mk(mt.idxTypes()), atomMapUpdate);
    check(tv, mt.elemType(), val);
    typeVarExit(atomMapUpdate);
    return memo(atomMapUpdate, mt);
  }
  // END visiting expressions }}}

  // BEGIN visiting commands {{{
  @Override public Type eval(AssignmentCmd assignmentCmd) {
    typeVarEnter(assignmentCmd);
    AstUtils.evalListOfOneAssignment(assignmentCmd.assignments(), this);
    typeVarExit(assignmentCmd);
    return null;
  }

  @Override public Type eval(OneAssignment oneAssignment) {
    Type lt = oneAssignment.lhs().eval(this);
    Type rt = oneAssignment.rhs().eval(this);
    check(rt, lt, oneAssignment);
    return null;
  }

  @Override public Type eval(AssertAssumeCmd assertAssumeCmd) {
    Type t = assertAssumeCmd.expr().eval(this);
    check(t, boolType, assertAssumeCmd);
    return null;
  }

  @Override public Type eval(CallCmd callCmd) {
    Procedure p = st.procs.def(callCmd);
    Signature sig = p.sig();
    ImmutableList<VariableDecl> fargs = sig.args();

    typeVarEnter(callCmd);

    // check the actual arguments against the formal ones
    Type at = typeListOfExpr(callCmd.args());
    Type fat = typeListOfDecl(fargs);
    check(at, fat, callCmd);

    // check the assignment of the results
    Type lt = typeListOfExpr(callCmd.results());
    Type rt = typeListOfDecl(sig.results());
    check(rt, lt, callCmd);

    typeVarExit(callCmd);

    return null;
  }
  // END visiting commands }}}

  // BEGIN check booleans {{{
  private Type checkBool(ImmutableList<Identifier> tv, Expr e) {
    enclosingTypeVar.push();
    collectEnclosingTypeVars(tv);
    check(e.eval(this), boolType, e);
    enclosingTypeVar.pop();
    return null;
  }

  @Override public Type eval(PostSpec postSpec) {
    return checkBool(postSpec.typeArgs(), postSpec.expr());
  }

  @Override public Type eval(PreSpec preSpec) {
    return checkBool(preSpec.typeArgs(), preSpec.expr());
  }

  @Override public Type eval(Axiom axiom) {
    return checkBool(axiom.typeArgs(), axiom.expr());
  }

  @Override public Type eval(VariableDecl variableDecl) {
    // TODO(radugrigore): check that the 'where' part is a boolean
    return null;
  }

  @Override public Type eval(ConstDecl constDecl) {
    // TODO(radugrigore): check that the 'where' part is a boolean
    return null;
  }
  // END check booleans }}}

  // BEGIN keep track of type variables {{{
  // NOTE: check all uses of enclosingTypeVar to see how all tracking is done
  @Override public Type eval(Procedure procedure) {
    enclosingTypeVar.push();
    collectEnclosingTypeVars(procedure.sig().typeArgs());
    AstUtils.evalListOfPreSpec(procedure.preconditions(), this);
    AstUtils.evalListOfPostSpec(procedure.postconditions(), this);
    AstUtils.evalListOfModifiesSpec(procedure.modifies(), this);
    enclosingTypeVar.pop();
    return null;
  }

  @Override public Type eval(Implementation implementation) {
    enclosingTypeVar.push();
    collectEnclosingTypeVars(implementation.sig().typeArgs());
    implementation.body().eval(this);
    enclosingTypeVar.pop();
    return null;
  }
  // END keep track of type variables }}}
}
