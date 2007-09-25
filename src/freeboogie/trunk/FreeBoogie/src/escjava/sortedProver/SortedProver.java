package escjava.sortedProver;

import java.io.File;
import java.util.Properties;

import escjava.sortedProver.NodeBuilder.SPred;

import freeboogie.util.Err;

public abstract class SortedProver {
  /* Variables indicating the state of the prover */

  /** Whether the prover was started. */
  public boolean started = false;

  /** Whether the background predicate was sent to the prover. */
  public boolean backgroundPredicateSent = false;

  /**
   * Start up the prover. After the prover is started correctly it should be
   * ready to receive any of the commands embodied by all the other methods of
   * this API.
   * 
   * @return a response code. A response code of {@link SortedProverResponse#OK}
   *         indicates that the prover started successfully and is ready to
   *         receive commands. A response code of {@link
   *         SortedProverResponse#FAIL} indicates that the prover did not start
   *         successfully and is not ready to receive commands. In the latter
   *         case, calling {@code getInfo()} on reponse object can revail
   *         additional arbitrary information about the failure.
   */
  public abstract SortedProverResponse startProver();

  /**
   * Get the {@link NodeBuilder} object that can be used to construct formulas
   * for the current prover.
   * 
   * @return a {@link NodeBuilder} object for the current prover.
   */
  public abstract NodeBuilder getNodeBuilder();

  /**
   * Send arbitrary information to the prover. Typically this information is not
   * mandatory and is only suggestions or informative information from the
   * front-end. This data is highly prover-dependent.
   * 
   * @param properties the set of property/value pairs to send to the prover.
   * @return a response code.
   */
  public abstract SortedProverResponse setProverResourceFlags(
    Properties properties);

  /**
   * Send the theory background predicate to the solver.
   * 
   * @return a response code.
   */
  public abstract SortedProverResponse sendBackgroundPredicate();

  /**
   * Declare a new axiom in the current theory.
   * 
   * @param formula
   * @return a response code.
   */
  public abstract SortedProverResponse declareAxiom(SPred formula);

  /**
   * Make an assumption.
   * 
   * @param formula the assumption to make.
   * @return a response code.
   */
  public abstract SortedProverResponse makeAssumption(SPred formula);

  /**
   * Retract some assumptions.
   * 
   * @param count the number of assumptions to retract.
   * @return a response code.
   */
  public abstract SortedProverResponse retractAssumption(int count);

  /**
   * Check the validity of the given formula given the current theory, its
   * axioms, and the current set of assumptions. The standard property names:
   * TimeLimit -- time limit in seconds ProblemName -- human readable name of
   * the problem (package.class.methodname(signature))
   * 
   * @param formula the formula to check.
   * @param callback the callbacks that will be called during the search
   * @param properties a set of hints, primarily resource bounds on this
   *          validity check.
   * @return a response code.
   */
  public abstract SortedProverResponse isValid(SPred formula,
    SortedProverCallback callback, Properties properties);

  /**
   * Stop the prover.
   * 
   * @return a response code.
   */
  public abstract SortedProverResponse stopProver();

  /**
   * Lookup and instantiate a new prover instance.
   * 
   * @param name the type of the prover to find
   * @return a SortedProver or null if the class was not found, if there are any
   *         other problems with the prover, it will print error message and
   *         abort.
   */
  public static SortedProver getProver(String name) {
    try {
      String firstLetter = name.substring(0, 1).toLowerCase();
      String tail = name.substring(1);
      String capName = firstLetter.toUpperCase() + tail;
      String nonCapName = firstLetter + tail;
      Class c = Class.forName("escjava.sortedProver." + nonCapName + "."
        + capName + "Prover");
      return (SortedProver)(c.newInstance());
    }
    catch (ClassNotFoundException e) {
      return null;
    }
    catch (IllegalAccessException e) {
      Err.fatal("problems instantiating prover (access): " + e);
      return null;
    }
    catch (InstantiationException e) {
      Err.fatal("problems instantiating prover (inst): " + e);
      return null;
    }
    catch (ClassCastException e) {
      Err.fatal("problems instantiating prover (cast): " + e);
      return null;
    }
  }

  /**
   * Encode the ProblemName from properties, which is supposed to be in the
   * 'package.subpackage.class.method(arg1,arg2)' format, into a
   * vcs/package/subpackage/class/method_arg1_arg2. Also create the directories
   * as needed.
   * 
   * @param properties
   */
  public static String encodeProblemName(Properties properties) {
    String methodName = properties.getProperty("ProblemName");
    StringBuffer fileBuf = new StringBuffer("vcs/");
    boolean afterParen = false;
    for (int i = 0; i < methodName.length(); ++i) {
      char c = methodName.charAt(i);
      switch (c) {
      case '.':
        if (!afterParen) c = '/';
        break;
      case '(':
        afterParen = true;
        c = '_';
        break;
      default:
        if (!((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9'))) c = '_';
        break;
      }
      fileBuf.append(c);
    }
    String filename = fileBuf.toString();
    while (filename.charAt(filename.length() - 1) == '_')
      filename = filename.substring(0, filename.length() - 1);
    String dirname = filename.substring(0, filename.lastIndexOf('/'));
    (new File(dirname)).mkdirs();
    return filename;
  }
}