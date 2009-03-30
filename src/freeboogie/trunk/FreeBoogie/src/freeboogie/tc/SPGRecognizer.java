package freeboogie.tc;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

/**
 * An implementation of an algorithm to recognize 
 * Series Parallel Graphs. It uses the algorithm
 * described in the paper: 
 * A New Algorithm for the Recognition of Series Parallel Graphs
 * by Berry Schoenmakers
 *
 * @author J. Charles (julien.charles@gmail.com)
 * @author reviewed by TODO
 */
public class SPGRecognizer<T> {
  private final SimpleGraph<T> graph;
  /** arcs in the spanning tree. */
  private final HashMap<T, T> pred = new HashMap<T, T>();
  /** remaining arcs. */
  private final HashMap<T, T> succ = new HashMap<T, T>();
  private int maxDeg;
  private final Map<T, Integer> topologicalNum = new HashMap<T, Integer> ();
  
  public SPGRecognizer(SimpleGraph<T> graph) {
    this.graph = graph;
  }
  
  public boolean check() {
    return initialization() && reductionStrategy();
  }
  
  /**
   * Annotates the graph with pred and succ annotations
   * The initialization phase (page 9 of the article)
   * 
   * @return false if the graph is not SP.
   */
  private boolean initialization() {
    T src = getSource(graph);
    LinkedList<T> q = new LinkedList<T>();
    q.add(src);
    
    
    while (q.size() > 0) {
      T x = q.removeFirst();

      for (T y: graph.to(x)) {
        if (pred.get(y) == null) {
          pred.put(y, x);
          q.addLast(y);
          if (succ.get(x) == null) {
            succ.put(x, y);
          }
        }
        else { // pred[y] != bottom
          if (succ.get(x) == null) {
            succ.put(x, y);
          }
          else {
            if (x == pred.get(succ.get(x))) {
              succ.put(x, y);
            }
            else {
              // not SP
              return false;
            }
          }
        }
      }
    }
    return true;
  }
  
  
  
  /**
   * Reduction algorithm that is on the page 10
   * @param x the selected redex
   * @return false if the graph is not SP.
   */
  private boolean reduction(T x) {
    T a = pred.get(x);
    T b = succ.get(x);
    boolean e = (a == pred.get(b) || succ.get(a) == b);
    if (!e) {
      if (x == pred.get(b)) {
        pred.put(b, a);
      }
      else {// x != pred.get(b)
        if (a == pred.get(succ.get(a))) {
          succ.put(a, b);
        }
        else {
          // not SP
          return false;
        }
      }
    }
    else {
      if (x == pred.get(b)) {
        // not SP
        return false;
      }
    }
    if (succ.get(a) == x) {
      succ.put(a, b);
    }
    return true;
  }
  
  
  @SuppressWarnings("unchecked")
  private boolean reductionStrategy() {
    Stack<T>[] bucketsTable = new Stack [maxDeg];
    for (int i = 0; i < maxDeg; i++) {
      bucketsTable[i] = new Stack<T> ();
    }
    for (T a: succ.keySet()) {
      if (isBlue(a)) {
        // a blue redex
        bucketsTable[d(a)].push(a);
      }
    }
    
    for (int i = 0; i < bucketsTable.length; i++) {
      while (!bucketsTable[i].empty()) {
        T curr = bucketsTable[i].pop();
        if (d(curr) == i) {

          Map<T, T> oldPred =  new HashMap<T,T>(pred);
          Map<T, T> oldSucc =  new HashMap<T, T>(succ);
          boolean res = reduction(curr);
          if (!res) {
            return false;
          }
          
          List<T> nodes = getChangeList(oldPred, oldSucc);
          for (T n : nodes) {
            if (isBlue(n)) {
              bucketsTable[d(n)].push(n);
            }
          }
        }
      }
    }
    return true;
  }

  
  private List<T> getChangeList(Map<T, T> oldPred, Map<T, T> oldSucc) {
    List<T> res = new ArrayList<T>();
    for (T n: succ.keySet()) {
      if (oldSucc.get(n) == null || oldPred.get(n) == null) {
        continue;
      }
      int oldDeg = f(oldSucc.get(n)) - f(oldPred.get(n));
      int deg = d(n);
      if (deg != oldDeg) {
        res.add(n);
      }
    }
    return res;
  }

  /**
   * IsBlue == (a != pred.get(b)) /\ (succ.get(a) = b)
   * @param a
   * @return true if (a, b) is blue
   */
  private boolean isBlue(T a) {
    T b = succ.get(a);
    return pred.get(b) != a;
  }

  private int d(T a) {
    return f(succ.get(a)) - f(pred.get(a));
  }

  /**
   * The function that returns the topological numbering
   * @param t
   * @return an integer >= 0
   */
  private int f(T t) {
    return topologicalNum.get(t);
  }

  /**
   * Returns the source node of the graph
   * @param graph
   * @return the first node of the graph
   */
  private T getSource(SimpleGraph<T> graph) {
    List<T> list = graph.nodesInTopologicalOrder();
    
    T res = list.get(0);
    
    for (T elem: list) {
      topologicalNum.put(elem, maxDeg);
      maxDeg++;
    }
    return res;
  }
  
  

}