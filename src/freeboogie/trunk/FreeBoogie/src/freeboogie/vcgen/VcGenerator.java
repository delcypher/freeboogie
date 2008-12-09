package freeboogie.vcgen;

import java.util.logging.Logger;

import freeboogie.ast.*;
import freeboogie.backend.*;
import freeboogie.tc.TcInterface;

/**
 * A facade for the {@code freeboogie.vcgen} package.
 *
 * The user can hand over an AST for preprocessing and then ask
 * for individual implementations to be checked. The prover to be
 * used is given by the user.
 */
public class VcGenerator<T extends Term> {
  /* IMPLEMENTATION
   *
   * The phases of VC generation are:
   *  (1) make graphs reducible TODO
   *  (2) infer invariants TODO
   *  (3) cut loops 
   *  (4) desugar calls 
   *  (5) desugar havoc
   *  (6) desugar where clauses TODO
   *  (7) desugar specifications 
   *  (8) make passive 
   *  (9) desugar maps, if the prover doesn't know about arrays
   * (10) desugar uniq on constants TODO
   * (11) desugar <: is prover doesn't know it TODO
   * (12) strongest postcondition 
   * (13) add axioms collected by the term builder TODO
   */

  private static final Logger log = Logger.getLogger("freeboogie.vcgen");

  private Declaration ast;
  private TcInterface tc;

  private LoopCutter loopCutter;
  private CallDesugarer callDesugarer;
  private HavocDesugarer havocDesugarer;
  private SpecDesugarer specDesugarer;
  private Passivator passivator;
  private MapRemover mapRemover;
  private FunctionRegisterer functionRegisterer;
  private AxiomSender axiomSender;

  private StrongestPostcondition<T> sp;

  private Prover<T> prover;
  private TermBuilder<T> builder;


  public VcGenerator() {
    loopCutter = new LoopCutter();
    callDesugarer = new CallDesugarer();
    havocDesugarer = new HavocDesugarer(); 
    specDesugarer = new SpecDesugarer();
    passivator = new Passivator();
    mapRemover = new MapRemover();
    functionRegisterer = new FunctionRegisterer();
    axiomSender = new AxiomSender();
    sp = new StrongestPostcondition<T>();
  }

  public void setProver(Prover<T> prover) throws ProverException {
    this.prover = prover;
    prover.push();
    preverify();
  }

  /**
   * Simplify {@code d} to a form where strongest postcondition
   * can be computed.
   */
  public Declaration process(Declaration d, TcInterface tc)
  throws ProverException {
    this.tc = tc;
    ast = loopCutter.process(d, tc);
    ast = callDesugarer.process(ast, tc);
    ast = havocDesugarer.process(ast, tc);
    ast = specDesugarer.process(ast, tc);
    ast = passivator.process(ast, tc);
    ast = mapRemover.process(ast, tc);
    preverify();
    return ast;
  }

  /**
   * Compute strongest postcondition and query the prover. This
   * {@code implementation} must be part the AST last processed.
   * Also, a prover must have been set.
   */
  public boolean verify(Implementation implementation) throws ProverException {
    assert prover != null && ast != null;
    sp.setFlowGraph(tc.getFlowGraph(implementation));
    T vc = sp.vc();
    return prover.isValid(vc);
  }

  // === helpers ===
  private void preverify() throws ProverException {
    if (prover == null || ast == null) return;
    builder = prover.getBuilder();
    sp.setBuilder(builder);
    builder.setTypeChecker(tc);
    functionRegisterer.setBuilder(builder);
    axiomSender.setProver(prover);
    builder.popDef();
    functionRegisterer.process(ast, tc);
    axiomSender.process(ast);
    builder.pushDef();
    prover.pop();
    // TODO add axioms
    prover.push();
  }
}
