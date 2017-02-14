package soot.jimple.infoflow.android.nu;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import soot.Local;
import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.ParameterRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.infoflow.android.resources.ARSCFileParser;
import soot.jimple.infoflow.nu.GlobalData;
import soot.jimple.infoflow.nu.GraphTool;
import soot.jimple.infoflow.nu.StmtPosTag;
import soot.jimple.toolkits.ide.icfg.BiDiInterproceduralCFG;
import soot.tagkit.StringConstantValueTag;
import soot.tagkit.Tag;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.Orderer;
import soot.toolkits.graph.PseudoTopologicalOrderer;
import soot.toolkits.graph.UnitGraph;
import soot.util.queue.QueueReader;

public class SharedPreferenceSearch {
	final String SET_SHARED_PREFERENCES = "android.content.SharedPreferences$Editor";
	BiDiInterproceduralCFG<Unit, SootMethod> cfg;
	public SharedPreferenceSearch(BiDiInterproceduralCFG<Unit, SootMethod> cfg){
		this.cfg = cfg;
	}
	
	public Set<Stmt> setSharedPreferencesSearch() {
		System.out.println("SEARCHING FOR SHARED PREFS");
		Set<Stmt> rs = new HashSet<Stmt>();
		int solvedCnt = 0;
		int unsolvedCnt = 0;
				
		
		for (QueueReader<MethodOrMethodContext> rdr =
				Scene.v().getReachableMethods().listener(); rdr.hasNext(); ) {
			SootMethod m = rdr.next().method();
			if(!m.hasActiveBody()) continue;
			
			UnitGraph g = new ExceptionalUnitGraph(m.getActiveBody());
		    Orderer<Unit> orderer = new PseudoTopologicalOrderer<Unit>();
		    int cnt = 0;
		    for (Unit u : orderer.newList(g, false)) {
		    	cnt++;
		    	Stmt s = (Stmt)u;
		    	if(!s.containsInvokeExpr()) continue;
		    	
		    	InvokeExpr ie = s.getInvokeExpr();
		    	SootMethod method = ie.getMethod();

		    	if(method.getSignature().contains(SET_SHARED_PREFERENCES) && method.getName().contains("put")) {
		    		Value v = ie.getArg(0);
		    		if(v instanceof Constant){
		    			//TODO: add constant to map
		    			System.out.println("Constant SharedPreference in Method: " + v);
		    			GlobalData global = GlobalData.getInstance();
		    			global.addPreferenceKey(v.toString());
		    			solvedCnt++;
		    			continue;
		    		}
		    		
		    		s.addTag(new StmtPosTag(cnt, m));
		    		System.out.println("NonConstant SharedPreference in Method:" + s);
		    		System.out.println("  DeclaringCls:"+cfg.getMethodOf(s).getDeclaringClass().getName());
		    		List<Tag> tt = s.getTags();
		    		if((tt != null))
		    			for(Tag t : tt)
		    				System.out.println("  TAG: "+t.toString());
		    		rs.add(s);
		    		GraphTool.displayGraph(g, m);
		    		//searchVariableDefs(g, s, v, new ArrayList<List<Object>>(), m);
		    		
		    		//v2
		    		String pref = findLastResStringAssignment(s, v, cfg, new HashSet<Stmt>());
		    		if(pref == null){
		    			System.out.println("  Failed to resolve this Pref.");
		    			unsolvedCnt++;
		    		}
		    		else{
		    			System.out.println("  Pref Key: "+pref);
		    			solvedCnt++;
		    			GlobalData global = GlobalData.getInstance();
		    			global.addPreferenceKey(pref);
		    			//global.addLayoutID(s, cfg, id);
		    		}
		    	}
		    }
		}
		System.out.println("JAMES: SHARED PREFERENCE SOLVED COUNT = " + solvedCnt);
		System.out.println("JAMES: SHARED PREFERENCE UNSOLVED COUNT = " + unsolvedCnt);
		return rs;
	}
	
	private String findLastResStringAssignment(Stmt stmt, Value target, BiDiInterproceduralCFG<Unit, SootMethod> cfg, Set<Stmt> visited) {
//		if (!doneSet.add(stmt))
//			return null;
		if(visited.contains(stmt)){
			return null;
		}
		visited.add(stmt);
		
		if(cfg == null) {
			System.err.println("Error: findLastResIDAssignment cfg is not set.");
			return null;
		}
		// If this is an assign statement, we need to check whether it changes
		// the variable we're looking for
		if (stmt instanceof AssignStmt) {
			AssignStmt assign = (AssignStmt) stmt;
			if (assign.getLeftOp() == target) {
				System.out.println("Debug: "+assign+" "+assign.getRightOp().getClass());
				// ok, now find the new value from the right side
				if (assign.getRightOp() instanceof StringConstant) {
					System.out.println("Debug: Assign was a constant");
					return ((StringConstant) assign.getRightOp()).value;
				} else if (assign.getRightOp() instanceof FieldRef) {
					System.out.println("Debug: Assign was field ref");
					SootField field = ((FieldRef) assign.getRightOp()).getField();
					for (Tag tag : field.getTags()){
						if (tag instanceof StringConstantValueTag){
							//System.out.println("This is an integerCOnstantValue");
							return ((StringConstantValueTag) tag).getStringValue();
						}
						else
							System.err.println("  Constant " + field + " was of unexpected type");
					}
					if(assign.getRightOp() instanceof StaticFieldRef){
						StaticFieldRef sfr = (StaticFieldRef)assign.getRightOp();
						/*if(sfr.getFieldRef().declaringClass().getName().endsWith(".R$id")){
							Integer id = valResParser.getResourceIDFromValueResourceFile(sfr.getFieldRef().name());
							if(id != null)
								return id;
						}
						*/
						System.out.println("  Field not assigned:"+sfr);
						target = assign.getRightOp();
					}
				} 
				else if(assign.getRightOp() instanceof Local){
					System.out.println("Debug: Assign was local");
					target = assign.getRightOp();
				}
				else if (assign.getRightOp() instanceof InvokeExpr) {
					System.out.println("Debug: Assign was invoke");
					InvokeExpr inv = (InvokeExpr) assign.getRightOp();
				}
			}
			
		}
		else if(stmt instanceof IdentityStmt){
			IdentityStmt is = (IdentityStmt)stmt;
			if(is.getLeftOp() == target){
				System.out.println("From IdentityStmt: "+is);
				if(is.getRightOp() instanceof ParameterRef){
					ParameterRef right = (ParameterRef)(is.getRightOp());
					int idx = right.getIndex();
					Collection<Unit> callers = cfg.getCallersOf(cfg.getMethodOf(stmt));
					if(callers != null && callers.size()>0){
						for(Unit caller : callers){
							System.out.println("  Caller: From IdentityStmt: "+caller);
							InvokeExpr ie = ((Stmt)caller).getInvokeExpr();
							if(idx >= ie.getArgCount())
								continue;
							Value arg = ie.getArg(idx);
							if(arg instanceof StringConstant)
								return ((StringConstant) arg).value;
							else{
								System.out.println("Still not integer");
								String lastAssignment = findLastResStringAssignment((Stmt) caller, arg, cfg, visited);
								if (lastAssignment != null)
									return lastAssignment;
							}
						}
					}
				}
			}
		}

		// Continue the search upwards
		for (Unit pred : cfg.getPredsOf(stmt)) {
			if (!(pred instanceof Stmt))
				continue;
			String lastAssignment = findLastResStringAssignment((Stmt) pred, target, cfg, visited);
			if (lastAssignment != null)
				return lastAssignment;
		}
		return null;
	}
	
}
