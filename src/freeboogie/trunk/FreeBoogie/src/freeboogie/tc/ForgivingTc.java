package freeboogie.tc;

import java.util.*;
import java.util.logging.Logger;
import freeboogie.ast.*;

// for debug
import java.io.PrintWriter;
import freeboogie.astutil.*;

/**
 * Typechecks the AST and modifies it a little if that will
 * fix errors. Code generated by Spec# that would otherwise
 * be illegal because certain constructs were modified/deprecated
 * in FreeBoogie should pass if this typechecker is used. The
 * modified AST, which satisfies all the rules of FreeBoogie,
 * can be retrieved.
 */
public class ForgivingTc extends Transformer implements TcInterface {

  private static final Logger log = Logger.getLogger("freeboogie.tc"); 

  // does the real work
  private TypeChecker tc;

  public ForgivingTc() {
    tc = new TypeChecker();
    tc.setAcceptOld(true);
  }

  @Override public Declaration getAST() { return tc.getAST(); }

  @Override
  public List<FbError> process(Declaration ast) {
    int oldErrCnt = Integer.MAX_VALUE;
    List<FbError> errors;
    while (true) {
      errors = tc.process(ast);
      ast = tc.getAST();
      int errCnt = errors.size();
      if (errCnt == 0 || errCnt >= oldErrCnt) break;
      oldErrCnt = errCnt;
      ast = fix(ast, errors);
      log.info("Running TypeChecker again.");
    }
    return errors;
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

  // this guy does most of the work
  private Declaration fix(Declaration ast, List<FbError> errors) {
    Inferrer inferrer = new Inferrer();
    Specializer specializer = new Specializer();

    HashMap<Expr, AtomId> filteredErrors = new HashMap<Expr, AtomId>();
    for (FbError e : errors) {
      switch (e.type()) {
      case REQ_SPECIALIZATION:
        filteredErrors.put((Expr)e.place(), (AtomId)e.data(2));
        break;
      default:
        // do nothing
      }
    }
    inferrer.process(ast, tc.getTypes());
    Map<Expr, Type> desired = inferrer.getGoodTypes();
    ast = specializer.process(
      ast, tc.getST(), filteredErrors, 
      desired, tc.getImplicitSpec());

    PrintWriter pw = new PrintWriter(System.out);
    PrettyPrinter pp = new PrettyPrinter(pw);
    ast.eval(pp);
    pw.flush();
    System.out.println("===END===");

    return ast;
  }
}
