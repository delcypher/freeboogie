package freeboogie.backend;

import java.math.BigInteger;
import java.util.*;

import com.google.common.collect.ImmutableList;
import genericutils.Err;

import freeboogie.ast.*;
import freeboogie.tc.*;

/**
 * Builds {@code Term}s out of Boogie expressions.
 *
 * NOTE that some Boogie expressions should be dealt with
 * earlier, such as the old() built-in.
 *
 * @param <T> the type of terms
 */
public class TermOfExpr<T extends Term<T>> extends Evaluator<T> {
  private TermBuilder<T> term;
  private TcInterface tc;
  private SymbolTable st;
  private Map<Expr, Type> typeOf;
  private Map<String, T> axioms = new HashMap<String, T>();

  public void setBuilder(TermBuilder<T> term) {
    this.term = term;
    axioms.put("literal_bool",
      term.mk("neq",
        term.mk("literal_bool", true),
        term.mk("literal_bool", false)));
    axioms.put("Tnand",
      term.mk("forall_bool", term.mk("var_bool", "a"),
      term.mk("forall_bool", term.mk("var_bool", "b"),
        term.mk("iff",
          term.mk("eq_bool",
            term.mk("Tnand",
              term.mk("var_bool", "a"),
              term.mk("var_bool", "b")),
            term.mk("literal_bool", true)),
          term.mk("not", term.mk("and",
            term.mk("eq_bool",
              term.mk("var_bool", "a"),
              term.mk("literal_bool", true)),
            term.mk("eq_bool",
              term.mk("var_bool", "b"),
              term.mk("literal_bool", true))))))));
    axioms.put("Tnand",
      term.mk("forall_bool", term.mk("var_bool", "a"),
      term.mk("forall_bool", term.mk("var_bool", "b"),
        term.mk("iff",
          term.mk("eq_bool",
            term.mk("Tnand",
              term.mk("var_bool", "a"),
              term.mk("var_bool", "b")),
            term.mk("literal_bool", false)),
          term.mk("and",
            term.mk("eq_bool",
              term.mk("var_bool", "a"),
              term.mk("literal_bool", true)),
            term.mk("eq_bool",
              term.mk("var_bool", "b"),
              term.mk("literal_bool", true)))))));
    axioms.put("T<",
      term.mk("forall_int", term.mk("var_int", "a"),
      term.mk("forall_int", term.mk("var_int", "b"),
        term.mk("iff",
          term.mk("eq_bool",
            term.mk("T<",
              term.mk("var_int", "a"),
              term.mk("var_int", "b")),
            term.mk("literal_bool", true)),
          term.mk("<",
            term.mk("var_int", "a"),
            term.mk("var_int", "b"))))));
    axioms.put("Teq",
      term.mk("forall", term.mk("var", "a"),
      term.mk("forall", term.mk("var", "b"),
        term.mk("iff",
          term.mk("eq_bool",
            term.mk("Teq", term.mk("var", "a"), term.mk("var", "b")),
            term.mk("literal_bool", true)),
          term.mk("eq", term.mk("var", "a"), term.mk("var", "b"))))));
    axioms.put("Teq_int",
      term.mk("forall_int", term.mk("var_int", "a"),
      term.mk("forall_int", term.mk("var_int", "b"),
        term.mk("iff",
          term.mk("eq_bool",
            term.mk("Teq_int",
              term.mk("var_int", "a"),
              term.mk("var_int", "b")),
            term.mk("literal_bool", true)),
          term.mk("eq_int",
            term.mk("var_int", "a"),
            term.mk("var_int", "b"))))));
    axioms.put("Teq_bool",
      term.mk("forall_bool", term.mk("var_bool", "a"),
      term.mk("forall_bool", term.mk("var_bool", "b"),
        term.mk("iff",
          term.mk("eq_bool",
            term.mk("Teq_bool",
              term.mk("var_bool", "a"),
              term.mk("var_bool", "b")),
            term.mk("literal_bool", true)),
          term.mk("iff",
            term.mk("eq_bool",
              term.mk("var_bool", "a"),
              term.mk("literal_bool", true)),
            term.mk("eq_bool",
              term.mk("var_bool", "b"),
              term.mk("literal_bool", true)))))));
  }

  public void setTypeChecker(TcInterface tc) {
    this.tc = tc;
    this.st = tc.st();
    this.typeOf = tc.types();
  }

  @Override public T eval(FunctionApp atomFun) {
    String prefix = "funT_";
    if (TypeUtils.isInt(typeOf.get(atomFun)))
      prefix = "funI_";
    if (TypeUtils.isBool(typeOf.get(atomFun)))
      prefix = "funB_";
    return term.mk(prefix + atomFun.function(), tuple(atomFun.args()));
  }

  @Override public T eval(Cast cast) {
    return cast.expr().eval(this);
  }

  @Override public T eval(Identifier atomId) {
    Type t = st.ids.def(atomId).type();
    if (TypeUtils.isInt(t)) {
      // this prefix is needed for z3, but not simplify
      return mk("var_int", "term$$" + atomId.id());
    } else if (TypeUtils.isBool(t)) {
      // add axiom that connects terms to formulas
      T result = mk("var_bool", "term$$" + atomId.id());
      result.addAxiom(term.mk("iff",
        term.mk("var_formula", atomId.id()),
        term.mk("eq_bool",
          term.mk("var_bool", "term$$" + atomId.id()),
          term.mk("literal_bool", true))));
      return result;
    } else {
      // this prefix is needed for z3, but not simplify
      return mk("var", "term$$" + atomId.id());
    }
  }

  @Override public T eval(BooleanLiteral atomLit) {
    switch (atomLit.val()) {
    case TRUE:
      return mk("literal_bool", true);
    case FALSE:
      return mk("literal_bool", false);
    default:
      assert false;
      return null;
    }
  }

  @Override public T eval(MapSelect atomMapSelect) {
    Type t = typeOf.get(atomMapSelect);
    String termId = "map_select";
    if (TypeUtils.isInt(t)) termId = "map_select_int";
    if (TypeUtils.isBool(t)) termId = "map_select_bool";
    return term.mk(
        termId, 
        atomMapSelect.map().eval(this), 
        term.mk("tuple", tuple(atomMapSelect.idx())));
  }

  @Override public T eval(MapUpdate atomMapUpdate) {
    return term.mk(
      "map_update", 
      ImmutableList.of(
          atomMapUpdate.map().eval(this), 
          term.mk("tuple", tuple(atomMapUpdate.idx())),
          atomMapUpdate.val().eval(this)));
  }

  @Override public T eval(NumberLiteral atomNum) {
    return term.mk("literal_int", atomNum.value());
  }

  @Override public T eval(Quantifier atomQuant) {
    // TODO can this be done without HOL?
    Err.internal("Quantifiers are not supported in this position.");
    return null;
  }

  @Override public T eval(BinaryOp binaryOp) {
    Expr left = binaryOp.left();
    Expr right = binaryOp.right();

    String termId = "***unknown***";
    Type lt = typeOf.get(left);
    Type rt = typeOf.get(right);
    T l = left.eval(this);
    T r = right.eval(this);
    switch (binaryOp.op()) {
    case PLUS:
      return mk("+", l, r);
    case MINUS:
      return mk("-", l, r);
    case MUL:
      return mk("*", l, r);
    case DIV:
      return mk("/", l, r);
    case MOD:
      return mk("%", l, r);
    case EQ: 
      if (TypeUtils.isBool(lt))
        return mk("Teq_bool", l, r);
      else if (TypeUtils.isInt(lt) && TypeUtils.isInt(rt)) 
        return mk("Teq_int", l, r);
      else
        return mk("Teq", l, r);
    case NEQ:
      if (TypeUtils.isBool(lt))
        return not(mk("Teq_bool", l, r));
      else if (TypeUtils.isInt(lt) && TypeUtils.isInt(rt))
        return not(mk("Teq_int", l, r));
      else
        return not(mk("Teq", l, r));
    case LT:
      return mk("T<", l, r);
    case LE:
      return or(mk("T<", l, r), mk("Teq_int", l, r));
    case GE:
      return or(mk("T<", r, l), mk("Teq_int", r, l));
    case GT:
      return mk("T<", l, r);
    case SUBTYPE:
      return mk("<:", l, r);
    case EQUIV:
      return mk("Tnand", mk("Tnand", l, r), or(l, r));
    case IMPLIES:
      return mk("Tnand", l, not(r));
    case AND:
      return not(mk("Tnand", l, r));
    case OR:
      return or(l, r);
    default:
      Err.internal("Unknown binary operator (" + binaryOp.op() + ").");
      return null;
    }
  }

  @Override public T eval(UnaryOp unaryOp) {
    String termId = "***unknown***";
    switch (unaryOp.op()) {
    case MINUS: 
      return mk(
          "-", 
          mk("literal_int", new FbInteger(new BigInteger("0"), -1)), 
          unaryOp.expr().eval(this));
    case NOT: 
      return not(unaryOp.expr().eval(this));
    default: assert false; return null;
    }
  }

  // === helpers ===
  private ImmutableList<T> tuple(ImmutableList<Expr> es) {
    ImmutableList.Builder<T> r = ImmutableList.builder();
    for (Expr e : es) r.add(e.eval(this));
    return r.build();
  }

  private T not(T t) {
    return mk("Tnand", t, t);
  }

  private T or(T x, T y) {
    return mk("Tnand", not(x), not(y));
  }

  private T decorate(String id, T t) {
    T a = axioms.get(id);
    if (a != null) t.addAxiom(a);
    return t;
  }

  private T mk(String id, Object a) {
    return decorate(id, term.mk(id, a));
  }

  private T mk(String id, T a) {
    return decorate(id, term.mk(id, a));
  }

  private T mk(String id, T a, T b) {
    return decorate(id, term.mk(id, a, b));
  }

  private T mk(String id, ArrayList<T> a) {
    return decorate(id, term.mk(id, a));
  }
}
