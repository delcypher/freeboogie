package freeboogie.ast;

import java.io.*;
import java.util.HashMap;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Maps;
import genericutils.*;

import freeboogie.tc.TcInterface;

/**
  Dumps flow graphs for all implementations in dot format.
 
  @author rgrig 
 */
@SuppressWarnings("unused") // unused parameters
public class FlowGraphDumper extends Transformer {
  private File directory;

  /* Don't run the internal typecheck. */
  @Override public Program process(Program program, TcInterface typechecker) {
    tc = typechecker;
    program.eval(this);
    return program;
  }

  public void directory(File directory) {
    Preconditions.checkArgument(directory.exists());
    this.directory = directory;
  }

  private String cmdToString(Command c) {
    StringWriter sw = new StringWriter();
    PrettyPrinter pp = new PrettyPrinter();
    pp.writer(sw);
    c.eval(pp);
    return sw.toString().replaceAll("\n", " ");
  }

  @Override public void see(Implementation impl) {
    Body body = impl.body();
    String name = 
      impl.sig().name() + 
      "_at_" + 
      impl.loc().toString().replace(':', '-');
    try {
      final PrintWriter w = new PrintWriter(new File(directory, name));
      SimpleGraph<Command> fg = tc.flowGraph(impl);
      w.println("digraph \"" + name + "\" {");
      final HashMap<Command, String> blockNames = Maps.newHashMap();
      fg.iterNode(new Closure<Command>() {
        @Override public void go(Command c) {
          String n = Id.get("L");
          blockNames.put(c, n);
          w.print("  \"" + n + "\" ");
          w.print("[shape=box,label=\""+cmdToString(c)+"\"]");
          w.println(";");
        }
      });
      if (!body.block().commands().isEmpty()) {
        w.println("  \"" + blockNames.get(body.block().commands().get(0)) + 
            "\" [style=bold];");
      }
      fg.iterEdge(new Closure<Pair<Command,Command>>() {
        @Override public void go(Pair<Command,Command> t) {
          w.println("  \"" + blockNames.get(t.first) + "\" -> \"" 
            + blockNames.get(t.second) + "\";");
        }});
      w.println("}");
      w.flush();
      w.close();
    } catch (FileNotFoundException e) {
      assert false : "PrintWriter should create the file.";
    }
  }
}
