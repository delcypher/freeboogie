package freeboogie;

import java.io.IOException;
import java.io.PrintWriter;

import ie.ucd.clops.runtime.options.InvalidOptionValueException;
import genericutils.Logger;

import freeboogie.cli.FbCliOptionsInterface;
import freeboogie.cli.FbCliParser;
import freeboogie.cli.FbCliUtil;

import static freeboogie.cli.FbCliOptionsInterface.*;
import static freeboogie.cli.FbCliOptionsInterface.LogCategories;
import static freeboogie.cli.FbCliOptionsInterface.LogLevel;

/**
  Handles the main pipeline of the application. The input/output
  data for various stages is one of: (1) a stream in the
  Boogie language format, (2) AST for representing Boogie, (3)
  s-expressions, (4) list of errors. The parser takes (1) as
  input and prouces (2). Then there are a few stages that take
  (2) as input and produce (2). The VC generation phase takes
  (2) as input and produces (3) as output. There are then a
  few stages that take (3) as input an produce (3) as output.
  Finally, the backend takes (3) as input and produces (4).

  NOTE: this is under development now and will replace both
  freeboogie.Main and freeboogie.vcgen.VcGenerator.
 */
public class AlternativeMain {

  private Logger<ReportOn, ReportLevel> out;
  private Logger<LogCategories, LogLevel> log;

  /** Process the command line and call {@code run()}. */
  public static void main(String[] args) throws Exception {
    FbCliParser p = new FbCliParser();
    try { if (!p.parse(args)) badUsage(); }
    catch (InvalidOptionValueException e) { badUsage(); }
    AlternativeMain m = new AlternativeMain();
    m.run(p.getOptionStore());
  }

  public void run(FbCliOptionsInterface opt) {
    if (opt.isHelpSet()) {
      FbCliUtil.printUsage();
      return;
    }

    // Setup logging and outputting.
    out = Logger.<ReportOn, ReportLevel>get("out");
    log = Logger.<LogCategories, LogLevel>get("log");
    out.sink(System.out); 
    out.level(opt.getReportLevel());
    for (ReportOn c : opt.getReportOn()) out.enable(c);
    try { log.sink(opt.getLogFile()); }
    catch (IOException e) { 
      out.say(
        ReportOn.MAIN,
        ReportLevel.VERBOSE, 
        "Can't write to log file " + opt.getLogFile() + ".");
    }
    log.level(opt.getLogLevel());
    for (LogCategories c : opt.getLogCategories()) log.enable(c);

    // Initialize required stages (parser, transformers, vc generator, backend).
    if (opt.getFiles().isEmpty())
      out.say(ReportOn.MAIN, ReportLevel.NORMAL, "Nothing to do. Try --help.");

    // For each file in the input.
      // Parse it.
      // Apply each transformer, conditionally.
      // Generate the VC.
      // Ask the prover.
  }

  public static void badUsage() {
    System.out.println("I don't understand what you want. Try --help.");
    System.exit(1);
  }
}
