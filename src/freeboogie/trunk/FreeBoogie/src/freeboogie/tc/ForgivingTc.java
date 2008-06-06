package freeboogie.tc;

import java.util.*;
import freeboogie.ast.*;

/**
 * Typechecks the AST and modifies it a little if that will
 * fix errors. Code generated by Spec# that would otherwise
 * be illegal because certain constructs were modified/deprecated
 * in FreeBoogie should pass if this typechecker is used. The
 * modified AST, which satisfies all the rules of FreeBoogie,
 * can be retrieved.
 */
public class ForgivingTc implements TcInterface {

  // does the real work
  private TypeChecker tc;

  // the (possibly modified) AST that is processed
  private Declaration ast;

  public ForgivingTc() {
    tc = new TypeChecker();
    tc.setAcceptOld(true);
  }

  @Override public Declaration getAST() { return ast; }

  @Override
  public List<FbError> process(Declaration ast) {
    // TODO: Implement
    assert false;
    return null;
  }

  @Override
  public SimpleGraph<Block> getFlowGraph(Implementation impl) {
    return tc.getFlowGraph(impl);
  }

  @Override
  public Map<Expr, Type> getTypes() {
    return tc.getTypes();
  }

  @Override
  public UsageToDefMap<Implementation, Procedure> getImplProc() {
    return tc.getImplProc();
  }

  @Override
  public UsageToDefMap<VariableDecl, VariableDecl> getParamMap() {
    return tc.getParamMap();
  }

  @Override
  public SymbolTable getST() {
    return tc.getST();
  }
}
