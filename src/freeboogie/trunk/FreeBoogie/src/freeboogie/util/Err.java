/** Public domain. */

package freeboogie.util;

/**
 * Provides basic facilities for reporting errors.
 * 
 * TODO: make the error reporting functions format the result;
 *       at least, they should make sure no more than 70 characters 
 *       per line are used
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class Err {
  
  /**
   * The possible verbosity levels. 
   */
  public enum Level {
    /** No output. */
    BATCH,
    
    /** Report only errors that make me stop. */
    FATAL,
    
    /** Report all problems. */
    ERROR,
    
    /** Give hints of what should be done to fix the problem. */
    HELP
  }
  
  /** The current verbosity level. */ 
  public static Level verboseLevel = Level.HELP;
  
  /**
   * Displays a help message.
   * @param h the help message
   */
  public static void help(String h) {
    if (verboseLevel.compareTo(Level.HELP) >= 0)
      System.err.println(h);
  }
  
  /**
   * Displays an error message.
   * @param e the error message
   */
  public static void error(String e) {
    System.err.println(e);
  }
  
  /**
   * Displays a fatal error end exits with code 1.
   * @param m the error message
   */
  public static void fatal(String m) {
    fatal(m, 1);
  }

  /**
   * Displays a fatal error and exits with the specified code.
   * @param m the error message
   * @param code the exit code
   */
  public static void fatal(String m, int code) {
    System.err.println(m);
    System.exit(code);
  }
  
  /** Aborts execution. */
  public static void notImplemented() {
    new Exception().printStackTrace();
    fatal("not implemented", 255);
  }
}