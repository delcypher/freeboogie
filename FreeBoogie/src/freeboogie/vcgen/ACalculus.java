package freeboogie.vcgen;

import java.util.HashMap;

import com.google.common.collect.Maps;
import genericutils.Logger;
import genericutils.SimpleGraph;

import freeboogie.Main;
import freeboogie.ast.*;
import freeboogie.backend.Term;
import freeboogie.backend.TermBuilder;
import freeboogie.tc.TcInterface;

import static freeboogie.cli.FbCliOptionsInterface.LogCategories;
import static freeboogie.cli.FbCliOptionsInterface.LogLevel;

/**
 * Base class for weakest precondition and strongest postcondition
 * implementations.
 * @param <T> the type of terms
 */
public abstract class ACalculus<T extends Term<T>> {
  /** the preconditions of each command. */
  protected final HashMap<Command, T> preCache = Maps.newHashMap();

  /** the postconditions of each command. */
  protected final HashMap<Command, T> postCache = Maps.newHashMap();

  /** builds terms for a specific theorem prover. */
  protected TermBuilder<T> term;

  protected T trueTerm;

  /** the control flow graph currently being processed. */
  protected SimpleGraph<Command> flow;

  protected boolean assumeAsserts;

  /** the current body which is being inspected. */
  private Body currentBody;

  private TcInterface tc;

  public void setBuilder(TermBuilder<T> term) {
    this.term = term;
    trueTerm = term.mk("literal_formula", Boolean.valueOf(true));
  }

  public void typeChecker(TcInterface tc) {
//System.out.println("really set " + (tc != null));
    this.tc = tc;
  }

  public void resetCache() {
    preCache.clear();
    postCache.clear();
  }

  public Body currentBody() {
    return currentBody;
  }

  /**
    Sets the implementation to be processed by subsequent calls to
    {@code pre}, {@code post}, and {@code vc}.
   */
  public void prepareFor(Implementation implementation) {
    flow = tc.flowGraph(implementation);
    Main.log.say(
        LogCategories.STATS,
        LogLevel.INFO,
        "cfg_size " + flow.nodeCount());
    currentBody = implementation.body();
    assert flow.isFrozen() : "please freeze flowgraph first";
    assert !flow.hasCycle() : "please cut loops first";
    resetCache();
  }

  /**
   * Returns a verification condition for the whole flow graph.
   * @return a term representing the vc
   */
  public abstract T vc();

  // === helpers ===
  public static boolean is(Command c, AssertAssumeCmd.CmdType t) {
    if (!(c instanceof AssertAssumeCmd)) return false;
    return ((AssertAssumeCmd)c).type() == t;
  }

  public static boolean isAssume(Command c) {
    return is(c, AssertAssumeCmd.CmdType.ASSUME);
  }

  public static boolean isAssert(Command c) {
    return is(c, AssertAssumeCmd.CmdType.ASSERT);
  }

  public T term(Command c) {
    if (!(c instanceof AssertAssumeCmd)) return trueTerm;
    return term.of(((AssertAssumeCmd)c).expr());
  }

  public TcInterface typeChecker() {
    return tc;
  }

  public void assumeAsserts(boolean assumeAsserts) {
    this.assumeAsserts = assumeAsserts;
  }
}
