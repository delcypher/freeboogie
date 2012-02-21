package freeboogie.backend;

import java.io.IOException;
import java.util.*;

import com.google.common.collect.ImmutableList;
import genericutils.Err;
import genericutils.Pair;

import freeboogie.Main;
import static freeboogie.cli.FbCliOptionsInterface.LogCategories;
import static freeboogie.cli.FbCliOptionsInterface.LogLevel;

/**
 * Used to interact with Simplify and Z3 (when run in Simplify
 * interactive <tt>/si</tt> mode).
 *
 * The responsibilities of this class are:
 *  (1) Prepare the {@code TermBuilder} by registering the
 *      appropriate symbols recognized by Simplify;
 *  (2) Unfold shared {@code SmtTerm}s by introducing temporary
 *      variables; (NOTE: the definitions should use FLET for Z3
 *      and IFF for simplify; TODO perhaps have two classes?)
 *  (3) Transform {@code SmtTerm} objects into the string
 *      representation;
 *  (4) TODO Take care of array axiomatization. Later on we should
 *      change this to take advantage of the built in arrays in Z3.
 *
 * @author rgrig
 */
public class SimplifyProver extends Prover<SmtTerm> {
  private SimplifyProcess simplify;
  private StringBuilder strBuilder;

  /**
   * Creates new {@code SimplifyProver}. It also tries to start the prover.
   *
   * @param cmd the command to use to start the prover
   * @throws ProverException if the prover cannot be started
   */
  public SimplifyProver(String[] cmd) throws ProverException {
    simplify = new SimplifyProcess(cmd);
    strBuilder = new StringBuilder();
    prepareTermBuilder();
  }

  /**
   * Prepares an {@code SmtTermBuilder} that knows about the
   * sorts and operators that Simplify understands.
   */
  private void prepareTermBuilder() {
    builder = new SmtTermBuilder();
  }

  // TODO treat everything that is registered in TermBuilder
  //      and drop the toUpperCase()
  private void printTerm(SmtTerm t, StringBuilder sb) {
    if (t.id.startsWith("var")) {
      sb.append((String)t.data);
    } else if (t.id.startsWith("forall")) {
      sb.append("(FORALL (");
      printTerm(t.children.get(0), sb);
      sb.append(") ");
      printTerm(t.children.get(1), sb);
      sb.append(")");
    } else if (t.id.equals("literal_int") || t.id.equals("literal")) {
      sb.append(t.data);
    } else if (t.id.equals("literal_bool")) {
      if ((Boolean)t.data)
        sb.append("term$$TRUE");
      else
        sb.append("term$$FALSE");
    } else if (t.id.equals("literal_formula")) {
      if ((Boolean)t.data)
        sb.append("TRUE");
      else
        sb.append("FALSE");
    } else if (t.id.equals("tuple")) {
      printArgs(t.children, sb);
    } else if (t.id.equals("distinct")) {
      sb.append("(DISTINCT ");
      printArgs(t.children, sb);
      sb.append(")");
    } else if (t.id.startsWith("cast")) {
      printTerm(t.children.get(0), sb);
    } else if (t.id.startsWith("eq")) {
      sb.append("(EQ ");
      printTerm(t.children.get(0), sb);
      sb.append(" ");
      printTerm(t.children.get(1), sb);
      sb.append(")");
    } else if (t.id.startsWith("neq")) {
      sb.append("(NEQ ");
      printTerm(t.children.get(0), sb);
      sb.append(" ");
      printTerm(t.children.get(1), sb);
      sb.append(")");
    } else if (t.id.startsWith("fun")) {
      sb.append("(");
      sb.append(t.id.substring(5));
      printArgs(t.children, sb);
      sb.append(")");
    } else {
      sb.append("(");
      sb.append(t.id.toUpperCase());
      printArgs(t.children, sb);
      sb.append(")");
    }
  }

  private void printArgs(List<SmtTerm> a, StringBuilder sb) {
    for (SmtTerm t : a) {
      sb.append(" ");
      printTerm(t, sb);
    }
  }

  protected void sendFatAssume(SmtTerm t) throws ProverException {
    strBuilder.setLength(0);
    strBuilder.append("(BG_PUSH ");
    printTerm(t, strBuilder);
    strBuilder.append(")");
    simplify.sendCommand(strBuilder.toString());
    log(strBuilder.toString());
  }

  @Override
  protected void sendAssume(SmtTerm t) throws ProverException {
    t = SmtTerms.eliminateSharing(t, builder);
    sendFatAssume(t);
  }

  @Override
  protected void sendRetract() throws ProverException {
    simplify.sendCommand("(BG_POP)");
    log("(BG_POP)");
  }

  @Override
  public boolean isValid(SmtTerm t) throws ProverException {
    Pair<SmtTerm, ImmutableList<SmtTerm>> p = SmtTerms.eliminateSharingPair(t, builder);
    sendFatAssume(builder.mk("and", p.second));
    strBuilder.setLength(0);
    printTerm(p.first, strBuilder);
    log(strBuilder.toString());
    long startTime = System.nanoTime();
    boolean r = simplify.isValid(strBuilder.toString());
    long endTime = System.nanoTime();
    long time = endTime - startTime;
    Main.log.say(
        LogCategories.STATS,
        LogLevel.INFO,
        String.format("provertime %.3fs", 1e-9*time));
    sendRetract();
    return r;
  }

  @Override
  public String[][] getLabels() {
    return simplify.getLabels();
  }

  @Override
  public void terminate() {
    simplify.stopProver();
    log("I tried to kill the prover. Hope it's dead.");
  }

  /**
   * Runs some basic tests.
   * @param args the command line arguments
   * @throws Exception thrown if something goes wrong
   */
  public static void main(String[] args) throws Exception {
    Prover<SmtTerm> p = new SimplifyProver(args);
    TermBuilder<SmtTerm> b = p.getBuilder();
    SmtTerm x = b.mk("var_pred", "x");
    SmtTerm y = b.mk("var_pred", "y");
    SmtTerm q = b.mk("not", b.mk("iff",
      b.mk("iff", b.mk("and", x, y), b.mk("or", x, y)),
      b.mk("iff", x, y)
    ));
    System.out.println("false = " + p.isValid(q));
  }
}
