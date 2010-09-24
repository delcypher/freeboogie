package freeboogie.vcgen;

import java.util.HashSet;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Sets;
import genericutils.Id;

import freeboogie.ast.*;
import freeboogie.tc.TcInterface;
import freeboogie.tc.TypeUtils;
import static freeboogie.ast.AstUtils.*;

/**
 * Replaces all map reads and writes by explicit calls to
 * <tt>select</tt> and <tt>update</tt>.
 */
public class MapRemover extends Transformer {
  private HashSet<Integer> arities = Sets.newHashSet();

  // TODO move in eval(Program...)
  @Override
  public Program process(Program p, TcInterface tc) {
    arities.clear();
    p = (Program) p.eval(this);
    if (arities.isEmpty()) return p;

    ImmutableList.Builder<FunctionDecl> functions = ImmutableList.builder();
    ImmutableList.Builder<Axiom> axioms = ImmutableList.builder();
    functions.addAll(p.functions());
    axioms.addAll(p.axioms());

    for (Integer n : arities) {
      // add "function $$selectN<TV, T1, ..., TN>
      //        (map : [T1, ..., TN]TV, x1 : T1, ..., xN : TN)
      //        returns (result : TV);"
      functions.add(mkFunctionDecl(
          "$$select", 
          n, 
          ImmutableList.<VariableDecl>of(), 
          mkType("TV")));

      // add "function $$updateN<TV, T1, ..., TN>
      //        (val : TV, map : [T1, ..., TN]TV, x1 : T1, ..., xN : TN)
      //        returns (result : [T1, ..., TN]TV);"
      functions.add(mkFunctionDecl(
          "$$update",
          n, 
          ImmutableList.of(mkVarDecl("val", mkType("TV"))),
          mkMapType(n)));

      // add "axiom<TV, T1, ..., TN>
      //        (forall m : [T1, ..., TN]TV, v : TV, x1 : T1, ..., xN : TN ::
      //          $$selectN($$updateN(v, m, x1, ..., xN), x1, ..., xN) == v
      //        );
      axioms.add(mkAxiom(
          ImmutableList.<Identifier>builder()
              .add(mkId("TV"))
              .addAll(nIds("T", n)).build(),
          ImmutableList.<VariableDecl>builder()
              .add(mkMapDecl("m", n))
              .add(mkVarDecl("v", mkType("TV")))
              .addAll(nVarDecl("x", n)).build(),
          mkEq(
              mkFun(
                  "$$select" + n,
                  ImmutableList.<Expr>builder()
                      .add(mkFun(
                          "$$update" + n,
                          ImmutableList.<Expr>builder()
                              .add(mkId("v"))
                              .add(mkId("m"))
                              .addAll(nExprs("x", n)).build()))
                      .addAll(nExprs("x", n)).build()),
              mkId("v"))));

      for (int i = n; i > 0; --i) {
        // "axiom<TV, T1, ..., TN>
        //    (forall m : [T1, ..., TN] TV, v : TV,
        //      x1 : T1, ..., xN : TN, y1 : T1, ..., yN : TN ::
        //      xi != yi ==>
        //      $$selectN($$updateN(v, m, x1, ..., xN), y1, ..., yN) ==
        //        $$selectN(m, y1, ..., yN));
        axioms.add(mkAxiom(
          ImmutableList.<Identifier>builder()
              .add(mkId("TV"))
              .addAll(nIds("T", n)).build(),
            ImmutableList.<VariableDecl>builder()
                .add(mkMapDecl("m", n))
                .add(mkVarDecl("v", mkType("TV")))
                .addAll(nVarDecl("x", n))
                .addAll(nVarDecl("y", n)).build(),
            mkImplies(
                mkNotEq(mkId("x" + i), mkId("y" + i)),
                mkEq(
                    mkFun(
                        "$$select" + n,
                        ImmutableList.<Expr>builder()
                            .add(mkFun(
                                "$$update" + n,
                                ImmutableList.<Expr>builder()
                                    .add(mkId("v"))
                                    .add(mkId("m"))
                                    .addAll(nExprs("x", n)).build()))
                            .addAll(nIds("y", n)).build()),
                    mkFun(
                        "$$select" + n,
                        ImmutableList.<Expr>builder()
                          .add(mkId("m"))
                          .addAll(nIds("y", n)).build())))));
      } // for i
    } // for n
    p = Program.mk(
        p.fileName(),
        p.types(),
        axioms.build(),
        p.variables(),
        p.constants(),
        functions.build(),
        p.procedures(),
        p.implementations(),
        p.loc());
    return TypeUtils.internalTypecheck(p, tc);
  }

  @Override public FunctionApp eval(MapSelect atomMapSelect) {
    Expr atom = atomMapSelect.map();
    ImmutableList<Expr> idx = atomMapSelect.idx();
    atom = (Expr) atom.eval(this);
    idx = AstUtils.evalListOfExpr(idx, this);
    int n = idx.size();
    arities.add(n);
    return mkFun(
        "$$select" + n, 
        ImmutableList.<Expr>builder().add(atom).addAll(idx).build());
  }

  @Override public FunctionApp eval(MapUpdate atomMapUpdate) {
    Expr atom = atomMapUpdate.map();
    ImmutableList<Expr> idx = atomMapUpdate.idx();
    Expr val = atomMapUpdate.val();
    atom = (Expr)atom.eval(this);
    idx = AstUtils.evalListOfExpr(idx, this);
    val = (Expr)val.eval(this);
    int n = idx.size();
    arities.add(n);
    return mkFun(
        "$$update" + n, 
        ImmutableList.<Expr>builder().add(val).add(atom).addAll(idx).build());
  }

  // === helpers ===

  // returns "function NAME<TV, T1, ..., TN>
  //            (ARGS, map : [T1,...,TN]TV, x1:T1,.., xN:TN)
  //            returns (result : RESULTYPE)
  private FunctionDecl mkFunctionDecl(
      String name, 
      int n,
      Iterable<VariableDecl> args,
      Type resultType
  ) {
    return FunctionDecl.mk(
        ImmutableList.<Attribute>of(),
        Signature.mk(
            name + n,
            ImmutableList.<Identifier>builder()
                .addAll(AstUtils.ids("TV"))
                .addAll(nIds("T", n)).build(),
            ImmutableList.<VariableDecl>builder()
                .addAll(args)
                .add(mkMapDecl("map", n))
                .addAll(nVarDecl("x", n)).build(),
            ImmutableList.of(VariableDecl.mk(
                ImmutableList.<Attribute>of(),
                "result",
                resultType,
                ImmutableList.<Identifier>of(),
                null))));
  }

  private Axiom mkAxiom(
      ImmutableList<Identifier> typeArgs,
      ImmutableList<VariableDecl> vars,
      Expr expr
  ) {
    return Axiom.mk(
        ImmutableList.<Attribute>of(),
        Id.get("map"),
        typeArgs,
        Quantifier.mk(
            Quantifier.QuantType.FORALL,
            AstUtils.ids(),
            vars,
            ImmutableList.<Attribute>of(),
            expr));
  }

  private VariableDecl mkVarDecl(String name, Type type) {
    return VariableDecl.mk(
        ImmutableList.<Attribute>of(), 
        name, 
        type, 
        ImmutableList.<Identifier>of(),
        null);
  }

  // returns "NAME : [T1,...,TN]TV"
  private VariableDecl mkMapDecl(String name, int n) {
    return mkVarDecl(name, mkMapType(n));
  }

  // returns "[T1,...,TN]TV"
  private MapType mkMapType(int n) {
    return MapType.mk(AstUtils.ids(), nTypes(n), mkType("TV"));
  }

  // returns "NAME" (as a user type)
  private UserType mkType(String name) {
    return UserType.mk(name, ImmutableList.<Type>of());
  }

  // TODO(rgrig): Is it really not possible to extract a MAP function??
  // returns "p1, ..., pN"
  private ImmutableList<Type> nTypes(int n) {
    ImmutableList.Builder<Type> types = ImmutableList.builder();
    for (int i = 1; i <= n; ++i) types.add(mkType("T" + i));
    return types.build();
  }
  private ImmutableList<Identifier> nIds(String prefix, int n) {
    ImmutableList.Builder<Identifier> ids = ImmutableList.builder();
    for (int i = 1; i <= n; ++i) ids.add(mkId(prefix + i));
    return ids.build();
  }

  // "safe" because all methods of ImmutableList<T> that take a T
  // argument already throw exceptions anyway.
  @SuppressWarnings("unchecked") 
  private ImmutableList<Expr> nExprs(String prefix, int n) {
    return (ImmutableList) nIds(prefix, n);
  }

  // returns "x1 : T1, ...., xN : TN"
  private ImmutableList<VariableDecl> nVarDecl(String prefix, int n) {
    ImmutableList.Builder<VariableDecl> decls = ImmutableList.builder();
    for (int i = 1; i <= n; ++i) 
      decls.add(mkVarDecl(prefix + i, mkType("T" + i)));
    return decls.build();
  }

  // returns "NAME(ARGS)" (as a function application)
  private FunctionApp mkFun(String name, Iterable<Expr> args) {
    return FunctionApp.mk(
        name, 
        ImmutableList.<Type>of(), 
        ImmutableList.<Expr>builder().addAll(args).build());
  }
}
