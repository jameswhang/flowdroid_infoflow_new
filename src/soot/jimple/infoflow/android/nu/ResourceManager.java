package soot.jimple.infoflow.android.nu;

import java.util.List;
import java.util.Map;

import soot.jimple.infoflow.android.resources.ARSCFileParser;
import soot.jimple.infoflow.android.resources.ARSCFileParser.AbstractResource;

public class ResourceManager {
	final static boolean debug = true;
	
	private ARSCFileParser resParser;
	private Map<Integer, List<String>> id2Texts;
	private Map<Integer, LayoutTextTreeNode> id2Node;
	private Map<String, LayoutTextTreeNode> layouts;
	private LayoutFileParserForTextExtraction lfpTE;
	
	public ResourceManager(String apkFileLocation, String appPackageName){
		resParser = new ARSCFileParser();
		try {
			resParser.parse(apkFileLocation);
		} catch (Exception e) {
			System.err.println("NULIST: failed to init FlowTriggerEventAnalyzer: ARSCFileParser");
			e.printStackTrace();
		}
		
		lfpTE = new LayoutFileParserForTextExtraction(appPackageName, resParser);
		lfpTE.parseLayoutFileForTextExtraction(apkFileLocation);
		id2Texts = lfpTE.getId2Texts();
		id2Node = lfpTE.getId2Node();
		layouts = lfpTE.getTextTreeMap();
		
		if(debug)
			displayResources();
	}
	
	public LayoutTextTreeNode getNodeById(int id){
		return id2Node.get(id);
	}
	public List<String> getTextsById(int id){
		return id2Texts.get(id);
	}
	public LayoutTextTreeNode getLayoutById(int id){
		AbstractResource ar = resParser.findResource(id);
		if (ar == null) return null;
		String layoutName = ar.getResourceName();
		return layouts.get(layoutName);
	}
	
	
	public void displayResources(){
		for(Integer id : lfpTE.getId2Type().keySet()){
			List<String> texts = id2Texts.get(id);
			String type = lfpTE.getId2Type().get(id);
			if(texts != null){
				for(String msg : id2Texts.get(id))
					System.out.println("VIEWTEXT: "+id+"("+type+") -> "+msg);
			}
			else if(type.endsWith("Layout") && id2Node.containsKey(id)){
				String text = id2Node.get(id).toStringTree(0,"");
			}
			else
				System.out.println("VIEWTEXT: "+id+"("+lfpTE.getId2Type().get(id)+") -> null");
		}
		for(String cls : layouts.keySet()){
			System.out.println(" LAYOUTTEXT: "+cls+" "+layouts.get(cls).toStringTree(0,""));
		}
	}
}
