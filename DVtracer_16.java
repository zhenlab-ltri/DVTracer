	// Copyright (C) 20081122 Taizo Kawano <tkawano at mshri.on.ca>
//
// This program is free software; you can redistribute it and/modify it 
// under the term of the GNU General Public License as published bythe Free Software Foundation;
// either version 2, or (at your option) any later version.
// 
// This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
// without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
// See the GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License
// along with this file.  If not, write to the Free Software Foundation,
// 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

// This imagej plugin is written for Calcium imaging analysis of movies that taken by dualview or equivalent beam splitter attached camera.
// Basically, this program requires user defined ROI only at left part, 
// and assume the left right alignment was nearly complete (with in a few pixel shift, depend on size of your ROI).
// Other wise, detecting same ROI at right part will be failed.
// Also, it is recommended that left half of image has brighter (may be yfp) part.
// ROI name should not contain ".".
//  .txt output files contains header and xy coordinate and mean intensity of ROIs.
// .png files shows left/right ratio of background subtracted rois.(bread through is not corrected)

// ver3. Right rois are not centered using center of math.
// Because in some slices right left right roi has slightly different position in previous version, and it cause bit noisy data.
// Now  initial 30 slices average lr shift are used to position rois to corresponding right part.
// ver4 implement bind roi. Also, if there is no designated background roi, use mean of half part as background value. 
// When start the plugin, dialg for frame inter will be shown. the time points are saved in output .txt file.
// ver5 calib.frameInterval; is used as frame interval. And if its 0.0, ask user to input it.
// system independent lineseparater
// CSV format(formar was tab)
// Jmalyze compatible output
// ver6. introduced rot roi, which is able to rotate particular roi around parent roi.
// This function was developed for non glued moving worm 
// ver7 again, search center at both images. The reason is it seems cause artifact when the worm move and rotated.
// ver8 panel control gui is introduced by plugin frame. For watching process, use different thread (DataCollect class).
// ver9 ratio image function was incorporated.
// ver10 extract xyx position data from meta data. 
// "xpos="+String.valueOf(xposarray[i])+",ypos="+String.valueOf(yposarray[i])+",zpos="+String.valueOf(zpos);
//also add roi width height data so that center of roi can plot.
// ver11 .ref function. use reference roi to locate initial position. 
// Then apply median filter, 2x resize, unsharpmask to search center. better for fast moving small rois.
// ver12 Replot and ratio data  function. fast data saving
// ver13 divide by left
// ver14 aim; function for not use right to align. how? .nr(xshift,yshift)?
// ver15 20151030 Search right incoorporated. This option always requirs assign shift.
// Now assin shift arrow esayer wayt to input "-" (minus). 
// ver16 20151030 Once run, show rois on the each slice. also added running median filter at plot.
// some case need .ref.nr() like assign.... cant handle current way. 
// solution; assign shift manually to all roi.
// also interrupt during processing. abort button.
// slice indicator in plot window
// # examin right tracking option. flip horizon is better? 
// if took later way, need save stage pos data again. (width + initial roi + width/2)%width?
// # later; also forward reverse detection? onecell.ax(another cell, angle)? 
// need value of calibration of magnification
// 120120 minor bug fix Ratio data result not correct if divide left
// 120127 ratio image can made right/left. also right brightness can use.


import java.awt.*;
import java.util.*;
import java.util.prefs.Preferences;
import java.io.*;
import ij.*;
import ij.process.*;
import ij.gui.*;
import ij.plugin.*;
import ij.plugin.filter.*;
import ij.plugin.frame.*;
import ij.io.*;
import ij.measure.*;
import java.awt.event.*;


public class DVtracer_16 extends PlugInFrame implements ActionListener,TextListener,ImageListener, ItemListener{
    
    Preferences prefs;
    ImagePlus imp;
    ImageProcessor ip;
    java.awt.Checkbox searchboth;
    java.awt.Checkbox fixedshift;
    java.awt.Checkbox jmalzecompatible;
    java.awt.Checkbox dividebyleft;
    java.awt.Checkbox rightforbrightness;//ratioimage with right brightness
    java.awt.Checkbox showroi;
    
    java.awt.Checkbox rightasref;//search roi at right image. always use fixed shift
    TextField upperlimittxt;
    TextField lowerlimittxt;
    TextField assignedxshifttxt;
    TextField assignedyshifttxt;
    TextField runmedwindowtxt;
    RoiManager Manager;
    java.awt.List Roilist;
    ImageStatistics imstat;
    boolean[] isfixed;
    boolean[] isbind;
    boolean[] isrot;
    boolean[] isref;
    int[][] bindinfo;
    double[][] rotinfo;
    double[][][] parentrotinfo;
    int[][] refinfo;//[roiindex][parentroi index,xshift from parent,yshift from parent] this must update every slice
    int[][] initialrefinfo;//use when you restart process
    int backgroundroiindex=-1;
    int[] indexes;
    Hashtable Rois;
    Roi[] initialRois;
    String[] roinamearray;
    Roi temproi;
    int width;
    int height;
    int slicenum;
    int[][] initialcoordinates;
    int[][] roiswidthheight;
    int refslicenum=30;//initial x slices for reference
    double frameinterval;
    int[][] avelrshiftofeachrois;
    double[] averagelrshift;
    double[][] output;
    ImagePlus leftim;
    ImagePlus impratio;
    ImageProcessor protip;
    ImagePlus plotimp;
    Plot plot;
    int previousslice=0;
	double plottedmin=0;
	double plottedmax=0;
    Roi lefthalf;
    Roi righthalf;
    double[][] posarray;
    double[] xindex=null;//for plot
    double[] xindex_filtered=null;
    double[][] yvalue=null;
    double[][] invertyvalue=null;
    double[][] filteredyval=null;
    DataCollect dc;
    boolean abortflag=false;
    int runmedwindow=3;
    
    public DVtracer_16() {
        super("DVtracer_16");
        ImagePlus.addImageListener(this);
        //WindowManager.addWindow(this);
        double upperlimit=10;
        double lowerlimit=2;
        int assignedshiftx=0;
        int assignedshifty=0;
        prefs = Preferences.userNodeForPackage(this.getClass());//make instance? 
        try 
        {
            upperlimit=Double.parseDouble(prefs.get("UPPER", "10")); 
            lowerlimit=Double.parseDouble(prefs.get("LOWER", "2")); 
            IJ.log("test upper "+String.valueOf(upperlimit)+ " lower "+String.valueOf(lowerlimit));
            assignedshiftx=Integer.parseInt(prefs.get("ASSIGNEDX", "0")); 
            assignedshifty=Integer.parseInt(prefs.get("ASSIGNEDY", "0")); 
            runmedwindow=Integer.parseInt(prefs.get("RUNMEDWINDOW", "0")); 
        }
        catch(java.lang.Exception e){}
        //Prepare GUI
        GridBagLayout gbl = new GridBagLayout();
        setLayout(gbl);
        GridBagConstraints gbc = new GridBagConstraints();
        //Button b;

        //Button addButton(String text, GridBagLayout gbl, int x, int y, int gridx_, int gridy_, int gridwidth){
        addButton("Locate Rois to center",gbl,120,20,0,0,4);
        addButton("Run",gbl,120,20,0,1,4);
        addButton("Restore Rois",gbl,120,20,0,2,4);
        
        searchboth = new Checkbox("Search both side", false);
        //.setPreferredSize(new Dimension(120,60));
        gbc.gridx=0;
        gbc.gridy=3;
        gbc.gridwidth= 4;
        gbl.setConstraints(searchboth,gbc);
        add(searchboth);
        
        fixedshift = new Checkbox("Assign shift", false);
        //.setPreferredSize(new Dimension(120,60));
        gbc.gridx=0;
        gbc.gridy=4;
        gbc.gridwidth= 4;
        gbl.setConstraints(fixedshift,gbc);
        add(fixedshift);

        Label labelxshift=new Label("x");
        gbc.gridx=0;
        gbc.gridy=5;
        gbc.gridwidth= 1;
        gbl.setConstraints(labelxshift,gbc);
        add(labelxshift);
        
        assignedxshifttxt = new TextField(String.valueOf(assignedshiftx), 3);
        assignedxshifttxt.addTextListener(this);
        assignedxshifttxt.setPreferredSize(new Dimension(60,20));
        gbc.gridx=1;
        gbc.gridy=5;
        gbc.gridwidth= 1;
        gbl.setConstraints(assignedxshifttxt,gbc);
        add(assignedxshifttxt);

        Label labelyshift=new Label("y");
        gbc.gridx=2;
        gbc.gridy=5;
        gbc.gridwidth= 1;
        gbl.setConstraints(labelyshift,gbc);
        add(labelyshift);
        
        assignedyshifttxt = new TextField(String.valueOf(assignedshifty), 3);
        assignedyshifttxt.addTextListener(this);
        assignedyshifttxt.setPreferredSize(new Dimension(60,20));
        gbc.gridx=3;
        gbc.gridy=5;
        gbc.gridwidth= 1;
        gbl.setConstraints(assignedyshifttxt,gbc);
        add(assignedyshifttxt);
        
	//inthe case that green and red has different pattern and right is better to track
	//alway use assing shift
        rightasref = new Checkbox("search at Right", false);
	rightasref.addItemListener(this);
        //.setPreferredSize(new Dimension(120,60));
        gbc.gridx=0;
        gbc.gridy=6;
        gbc.gridwidth= 4;
        gbl.setConstraints(rightasref,gbc);
        add(rightasref);

        //for green/red sensor
        dividebyleft = new Checkbox("Divide by leftt", false);
        //.setPreferredSize(new Dimension(120,60));
        gbc.gridx=0;
        gbc.gridy=7;
        gbc.gridwidth= 4;
        gbl.setConstraints(dividebyleft,gbc);
        add(dividebyleft);
        
        jmalzecompatible = new Checkbox("Jmalyze format", false);
        //.setPreferredSize(new Dimension(120,60));
        gbc.gridx=0;
        gbc.gridy=8;
        gbc.gridwidth= 4;
        gbl.setConstraints(jmalzecompatible,gbc);
        add(jmalzecompatible);

        addButton("Ratio image",gbl,120,20,0,9,4);
        addButton("Ratio with brightness",gbl,120,20,0,10,4);

        rightforbrightness= new Checkbox("Use Right brightness", false);
        //.setPreferredSize(new Dimension(120,60));
        gbc.gridx=0;
        gbc.gridy=11;
        gbc.gridwidth= 4;
        gbl.setConstraints(rightforbrightness,gbc);
        add(rightforbrightness);
        
        addButton("Replot",gbl,120,20,0,12,4);

        Label lower=new Label("min");
        gbc.gridx=0;
        gbc.gridy=13;
        gbc.gridwidth= 1;
        gbl.setConstraints(lower,gbc);
        add(lower);

        lowerlimittxt = new TextField(String.valueOf(lowerlimit), 3);
        lowerlimittxt.setPreferredSize(new Dimension(60,20));
        gbc.gridx=1;
        gbc.gridy=13;
        gbc.gridwidth= 1;
        gbl.setConstraints(lowerlimittxt,gbc);
        add(lowerlimittxt);
        
        Label upper=new Label("max");
        gbc.gridx=2;
        gbc.gridy=13;
        gbc.gridwidth= 1;
        gbl.setConstraints(upper,gbc);
        add(upper);

        upperlimittxt = new TextField(String.valueOf(upperlimit), 3);
        upperlimittxt.setPreferredSize(new Dimension(60,20));
        gbc.gridx=3;
        gbc.gridy=13;
        gbc.gridwidth= 1;
        gbl.setConstraints(upperlimittxt,gbc);
        add(upperlimittxt);

        Label runmed=new Label("run med");
        gbc.gridx=0;
        gbc.gridy=14;
        gbc.gridwidth= 2;
        gbl.setConstraints(runmed,gbc);
        add(runmed);

        runmedwindowtxt = new TextField(String.valueOf(runmedwindow), 2);
        runmedwindowtxt.addTextListener(this);
        runmedwindowtxt.setPreferredSize(new Dimension(60,20));
        gbc.gridx=2;
        gbc.gridy=14;
        gbc.gridwidth= 1;
        gbl.setConstraints(runmedwindowtxt,gbc);
        add(runmedwindowtxt);
	
	
        showroi= new Checkbox("show roi after process", true);
	showroi.addItemListener(this);
        gbc.gridx=0;
        gbc.gridy=15;
        gbc.gridwidth= 4;
        gbl.setConstraints(showroi,gbc);
        add(showroi);


        addButton("Ratio data",gbl,120,20,0,16,4);
        addButton("Abort",gbl,120,20,0,17,4);

        GUI.center(this);
        setSize(130,380);
        setVisible(true);
    }
    
    Button addButton(String text){
        Button b;
        b = new Button(text);
        b.addActionListener(this);
        //add(b);
        return b;
    }
    Button addButton(String text, GridBagLayout gbl, int x, int y, int gridx_, int gridy_, int gridwidth){
        GridBagConstraints gbc = new GridBagConstraints();
    	Button b= new Button(text);
        b.addActionListener(this);
    	b.setPreferredSize(new Dimension(x,y));
    	gbc.gridx=gridx_;
    	gbc.gridy=gridy_;
    	gbc.gridwidth= gridwidth;
    	gbc.weightx=100;
    	gbc.weighty=100;
    	gbc.fill = GridBagConstraints.BOTH ; 
    	gbl.setConstraints(b,gbc);
    	add(b);
    	return b;
    }
    
    public void windowClosed(java.awt.event.WindowEvent e) 
    {
    	//IJ.log("closed 2");
    	ImagePlus.removeImageListener(this);
    }
    
    public void imageOpened(ImagePlus imp_) {}
    //when you scroll, show virtical line at plot correspond to the slice.
    public void imageUpdated(ImagePlus imp_) {
        if(imp_.equals(imp)&&output!=null&&plotimp!=null&&plot!=null)
        {
		//IJ.log("image up and output!=null etc.");
        	if(dc.isAlive())
        	{
        		return;
        	}
        	if(previousslice!=imp.getSlice())
        	{
			//IJ.log("previous!=now");
        		previousslice=imp.getSlice();
	            //IJ.log("image updated slice "+String.valueOf(imp.getSlice()));
	            //protip
	            ImageProcessor protip = plotDivideddata(plot, imp.getShortTitle(), plottedmin, plottedmax, runmedwindow);
	            plot.drawLine((double)imp.getSlice(), plottedmin, (double)imp.getSlice(),plottedmax );
	            protip=plot.getProcessor();
	            plotimp.setProcessor(null,protip);
	            /*this may or may not fast?
	            Plot indicaterplot=new Plot("plot","slicenum","ratio",new double[]{0.0},new double[]{0.0});
	            indicaterplot.setLimits(0,slicenum,plottedmin,plottedmax);
	            indicaterplot.drawLine((double)imp.getSlice(), plottedmin, (double)imp.getSlice(),plottedmax );
	            ImageProcessor ipi=indicaterplot.getProcessor();
	            //calculate or marge two ip...
	            plotimp.setProcessor(null,protip);
	            */
		    
		    //show rois on the image
			overlayRois();
       		}
        }
    }
    
    void overlayRois()
    {
	ImageCanvas ic=imp.getCanvas();
	ic.setShowAllROIs(false);//DONT show all Rois.
	Overlay overlay= new Overlay();
	if(imp.getOverlay()!=null)
	{
		overlay=imp.getOverlay();
	}
	//IJ.log("clear");
	overlay.clear();
	if(!showroi.getState())
	{
		return;
	}
	for(int i=0;i<indexes.length;i++)
	{
		Roi temproi=(Roi) Rois.get(Roilist.getItem(indexes[i]));
		
		Roi drawingroi1 = cloneRoi(temproi);
		drawingroi1.setLocation((int)output[imp.getSlice()-1][i*3],(int)output[imp.getSlice()-1][i*3+1]);
		overlay.add(drawingroi1);
		
		Roi drawingroi2 = cloneRoi(temproi);
		drawingroi2.setLocation((int)output[imp.getSlice()-1][(indexes.length)*3+i*3],(int)output[imp.getSlice()-1][(indexes.length)*3+i*3+1]);
		overlay.add(drawingroi2);
	}
	//IJ.log("overlay.size() "+String.valueOf(overlay.size()));
	imp.setOverlay(overlay); 
    }
    
    //only works with oval, polygon, rectangle roi. not for freehand, line etc.
    Roi cloneRoi(Roi roi)
    {
    	Roi returnroi;
	java.awt.Rectangle boundary=roi.getBounds();
	if(roi instanceof OvalRoi)
	{
		//IJ.log("oval");
		returnroi=new OvalRoi(boundary.x, boundary.y, boundary.width, boundary.height);
	}
	else if(roi instanceof PolygonRoi)
	{
		//IJ.log("polygon");
		java.awt.Polygon poly= roi.getPolygon();
		returnroi=new PolygonRoi(poly.xpoints, poly.ypoints, poly.npoints, roi.getType());
	}
	else
	{
		//treat as rectanglar
		//IJ.log("rect");
		returnroi=new Roi(boundary.x, boundary.y, boundary.width, boundary.height);
	}
	return returnroi;
    }
    
    public void imageClosed(ImagePlus impc) {
        //Write logic to clear valables when image closed here 
        if(imp==impc)
        {
            //IJ.log("The image closed");
            imp=null;
            output=null;
            averagelrshift=null;
            leftim=null;
            impratio=null;
            plotimp=null;
            plot=null;
	    filteredyval=null;
            dc=null;
        }
        else
        {
            IJ.log("something else closed");
        }
    }
    

	public void itemStateChanged(ItemEvent e) {
		//IJ.log(e.paramString());
		String lable=(String)e.getItem();
		//here when rightasref checkbox is checked, automatically enable assign shift.
		if(lable.equals("search at Right"))
		{
			int state = e.getStateChange();
			if (state == e.SELECTED)
			{
				fixedshift.setState(true);
			}
		}
		else if(lable.equals("show roi after process"))
		{
			if(output!=null&&plotimp!=null&&plot!=null)
			{
				int state = e.getStateChange();
				if (state == e.SELECTED)
				{
					overlayRois();
				}
				else
				{
					Overlay overlay= new Overlay();
					if(imp.getOverlay()!=null)
					{
						overlay=imp.getOverlay();
					}
					IJ.log("clear");
					overlay.clear();
					imp.draw();
				}
			}
		}
        }
	
	//assign sift changed
    public void textValueChanged(TextEvent e)
    {
    	IJ.log("text changed "+e.toString() );
    	IJ.log(e.getSource().toString());
    	TextField tf;
    	tf=(TextField)e.getSource();
    	if(tf==assignedxshifttxt)
    	{
    		IJ.log("shiftx");
		if(tf.getText().equals("-") || tf.getText().equals("0-"))
			return;
    		//fieldvaluearray[0]
    		//arg(tf, index of fieldvaluearray, min, max)
    		int[] ci=checkInt(tf, -10, 10);
    		if(ci[0]==0)
    		{
    			prefs.put("ASSIGNEDX", String.valueOf(ci[1])); //save in the preference
    		}
    		else
    		{
    			tf.setText(prefs.get("ASSIGNEDX", "0"));
    		}
    	}
    	else if(tf==assignedyshifttxt)
    	{
    		IJ.log("shifty");
		if(tf.getText().equals("-") || tf.getText().equals("0-"))
			return;
    		//fieldvaluearray[0]
    		//arg(tf, index of fieldvaluearray, min, max)
    		int[] ci=checkInt(tf, -10, 10);
    		if(ci[0]==0)
    		{
    			prefs.put("ASSIGNEDY", String.valueOf(ci[1])); //save in the preference
    		}
    		else
    		{
    			tf.setText(prefs.get("ASSIGNEDY", "0"));
    		}
    	}
    	else if(tf==lowerlimittxt)
    	{
    		//may need something
    	}
    	else if(tf==upperlimittxt)
    	{
    		//may need something    		
    	}
    	else if(tf==runmedwindowtxt)
    	{
		if(tf.getText().equals("-") || tf.getText().equals("0-"))
			return;
    		int[] ci=checkInt(tf, 0, 100);
    		if(ci[0]==0)
		{
			runmedwindow=Integer.parseInt(runmedwindowtxt.getText());
    			prefs.put("RUNMEDWINDOW", String.valueOf(ci[1])); //save in the preference
			IJ.log(String.valueOf(runmedwindow));
			filteredyval=null;
			if(output!=null&&plotimp!=null&&plot!=null)
			{
				//IJ.log("if(output!=null&&plotimp!=null&&plot!=null)");
				if(dc.isAlive())
				{
					//IJ.log("return");
					return;
				}
				//IJ.log("ploting");
				ImageProcessor protip = plotDivideddata(plot, imp.getShortTitle(), plottedmin, plottedmax, runmedwindow);
				plot.drawLine((double)imp.getSlice(), plottedmin, (double)imp.getSlice(),plottedmax );
				protip=plot.getProcessor();
				plotimp.setProcessor(null,protip);
			}
		}
		else
		{
			tf.setText(prefs.get("RUNMEDWINDOW", "0"));
		}
    	}
    }
    
    //the first num indicating if the tf can parse to int. 
    //0=ok, 1=out of range, -1=not number
    //second is int vale if possible
    int[] checkInt(TextField tf, int min, int max)
    {
        int[] testint=new int[] {0,0};
        try
        {
            testint[1] = Integer.parseInt(tf.getText());
            if(testint[1]>=min && testint[1]<=max)
            {
            	return testint;
            }
            else
            {
            	IJ.log("not valid range");
            	testint[0]=1;
            	return testint;
            }
        } catch (Exception ex) {
            IJ.log("It is not valid as a number.");
            testint[0]=-1;
            return testint;
        }    	
    }
    
    public void actionPerformed(ActionEvent e){
        ImagePlus currentimp=WindowManager.getCurrentImage();
        if(currentimp==null)
        {
            IJ.log("no image");  
            return;
        }
        if(currentimp.getBitDepth()==16)//only accept 16 bit image as source imp this is for exclude RGB or 32 bit ratio
        {
            IJ.log("16 bit");
            imp=currentimp;
        }
        //if(true) return;
        IJ.log(imp.getShortTitle());
        ip=imp.getProcessor();
        String lable =e.getActionCommand();
        IJ.log(lable);
        //IJ.log(String.valueOf(leftonly.getState()));
        //ip.invert();
        //imp.updateAndDraw();
        if(lable.equals("Locate Rois to center"))
        {
            imp.setSlice(1);
            prepImageinfo();
            IJ.log(String.valueOf(slicenum));
            measureMeanofRois(ip, imp,0,0);
        }
        else if (lable.equals("Run"))
        {
            //startTrace();
	    if(imp.getOverlay()!=null)
	    {
	    	imp.setHideOverlay(true);
	    }
            dc= new DataCollect(this);
            dc.start();
        }
        else if(lable.equals("Restore Rois"))
        {
            restoreRoipositions();
            imp.setSlice(1);
        }
        else if(lable.equals("Ratio image"))
        {
            //Roi halfofimageroi=new Roi(0,0,imp.getWidth()/2,imp.getHeight());
            //ip.setRoi(halfofimageroi);
            //ip=ip.crop();
            //ImageProcessor dup=ip.duplicate();
            //ImagePlus dupimage = new ImagePlus("dup", dup);
            //dupimage.show();
            //IJ.log(String.valueOf(output.length));
            if(output==null)
            {
                //IJ.log("Need to measure(run) the image first.");
                //return;
                IJ.showMessage("No measurement data found. Just make left/right ratio image without shift correction.");
                //prepImageinfo();//need roi
                slicenum=imp.getImageStackSize();
            }
            //if(true) return;
            Duplicater duplicater= new Duplicater();
            int lroix=0;
            int lroiy=0;
            int rroix=imp.getWidth()/2;
            int rroiy=0;
            int xsift=0;
            int ysift=0;
            int roiwidth=imp.getWidth()/2;
            int roiheight=imp.getHeight();
            if(averagelrshift==null)// check if averagelrshift is available
            {
                // just use half for now. In future, calculate avelage shift.
                //Roi lefthalf=new Roi(lroix,lroiy,roiwidth,roiheight);
            }
            else
            {
                IJ.log("averagelrshift x "+String.valueOf(averagelrshift[0]));
                IJ.log("averagelrshift y "+String.valueOf(averagelrshift[1]));
                IJ.log("half of width "+String.valueOf(imp.getWidth()/2));
                xsift=(int)(averagelrshift[0]-imp.getWidth()/2);
                ysift=(int)(averagelrshift[1]);
		if(rightasref.getState())
		{
			xsift=(int)(Math.abs((int)averagelrshift[0])-imp.getWidth()/2);
			ysift=-ysift;
		}
                IJ.log("xshift "+String.valueOf(xsift));
                roiwidth=(int)(imp.getWidth()/2-Math.abs(xsift));
                roiheight=imp.getHeight()-Math.abs((int)averagelrshift[1]);
                if(xsift>=0)
                {
                    lroix=0;
                    rroix=imp.getWidth()/2+xsift;
                    IJ.log("rroix "+String.valueOf(rroix));
                }
                else
                {
                    lroix=-xsift;
                    rroix=imp.getWidth()/2;
                }
                if(ysift>=0)
                {
                    lroiy=0;
                    rroiy=ysift;
                }
                else
                {
                    lroiy=-ysift;
                    rroiy=0;
                }
            }
            //IJ.log("here? "+String.valueOf(lroix)+" "+String.valueOf(lroiy)+" "+String.valueOf(rroix)+" "+String.valueOf(rroiy));
            lefthalf=new Roi(lroix,lroiy,roiwidth,roiheight);
            imp.setRoi(lefthalf);
            leftim=duplicater.duplicateStack(imp, "left");
            //subtract backgound left half
            for(int i=0;i<slicenum;i++)
            {
                leftim.setSlice(i+1);
                ImageProcessor ips=leftim.getProcessor();
                if(output==null)
                {
                    leftim.setRoi(lefthalf);
                    ImageStatistics stat=leftim.getStatistics(2);//MEAN=2    }
                    ips.add(-stat.mean);
                }
                else
                {
                    ips.add(-output[i][backgroundroiindex*3+2]);
                }
            }
            //leftim.show();
            //if(true) return;
            StackConverter Stcon=new StackConverter(leftim);
            Stcon.convertToGray32() ;
            //Due to less memory or huge data whatever, change logic so that use lesser amount of memory
            righthalf=new Roi(rroix,rroiy,roiwidth,roiheight);
            for(int i=0;i<slicenum;i++)
            {
                imp.setSlice(i+1);
                imp.setRoi(righthalf);
                ImageProcessor ips=imp.getProcessor().crop();
                if(output==null)
                {
                    //IJ.log(String.valueOf(i));
                    ImageStatistics stat=imp.getStatistics(2);//MEAN=2    }
                    ips.add(-stat.mean);
                }
                else
                {
                    ips.add(-output[i][indexes.length*3+backgroundroiindex*3+2]);
                }
                //
                ImageProcessor ips32=ips.convertToFloat();
                leftim.setSlice(i+1);
                ImageProcessor ipsleft=leftim.getProcessor();
                //ipsleft=leftim.getProcessor();
                //ipsleft.convertToFloat();//is it already float
                if(dividebyleft.getState())
                {
                	//IJ.log("through?");
                	//ImageProcessor ipstemp=ipsleft.duplicate();
                	//ipsleft.
                	ips32.copyBits(ipsleft,0,0,6);//DIVIDE = 6;
                	ipsleft.copyBits(ips32,0,0,0);//COPY = 0
                	
                	/*
                	ImagePlus testimpips=new ImagePlus("ips",ips32);
                	testimpips.show();
                	ImagePlus testimpleft=new ImagePlus("ipsleft",ipsleft);
                	testimpleft.show();
                	return;
                	*/
                }
                else
                {
                	ipsleft.copyBits(ips32,0,0,6);//DIVIDE = 6;
                }
            }
            
            ImageProcessor ipl=leftim.getProcessor();
            LutLoader LutL=new LutLoader();
            WindowManager.setTempCurrentImage(leftim);
            LutL.run("spectrum");
            //LutL.run("Rainbow RGB");//this lut is not included in all distribution
            ipl.invertLut();
            IJ.run("Enhance Contrast", "saturated=0.5");
            leftim.setTitle("ratio.tif"); 
            leftim.show();
            
        }
        else if(lable.equals("Ratio with brightness"))
        {
            //ImageProcessor ipratio=impratio.getProcessor();
            //ipratio.convertToRGB();
            if(leftim==null)
            {
                IJ.showMessage("No ratio imaged found. Please prep ratio image first.");
                return;
            }
            //StackConverter sc=new StackConverter(impratio);
            StackConverter sc=new StackConverter(leftim);
            //ImagePlus imprgb=new ImagePlus("rgb", ipratio);
            sc.convertToRGB();
            /*
            //test
                imp.setSlice(1);
                imp.setRoi(lefthalf);
                ImageProcessor testips=imp.getProcessor().crop();//normaly it is 16bit. Don't consider other case for now.
                testips=testips.convertToByte(true);
                leftim.setSlice(1);
                ImageProcessor testipl=leftim.getProcessor();
                IJ.log(String.valueOf(testipl.getPixel(1,1)));
                FloatProcessor testflp=testipl.toFloat(0,null);
                IJ.log(String.valueOf(Float.intBitsToFloat(testflp.getPixel(1,1))));
                testflp.copyBits(testips,0,0,5);//MULTIPLY = 5;
                IJ.log(String.valueOf(Float.intBitsToFloat(testflp.getPixel(1,1))));
                testflp.multiply((1.0/255));
                IJ.log(String.valueOf(Float.intBitsToFloat(testflp.getPixel(1,1))));
                testipl.setPixels(0,testflp);
                testflp=testipl.toFloat(1,null);
                testflp.copyBits(testips,0,0,5);//MULTIPLY = 5;
                testflp.multiply((1.0/255));
                testipl.setPixels(1,testflp);
                testflp=testipl.toFloat(2,null);
                testflp.copyBits(testips,0,0,5);//MULTIPLY = 5;
                testflp.multiply((1.0/255));
                testipl.setPixels(2,testflp);
            //endtest
            if(true) return;
            */
            for(int i=0;i<slicenum;i++)
            {
                imp.setSlice(i+1);
                if(rightforbrightness.getState())
                {
                	imp.setRoi(righthalf);                	
                }
                else
                {
                	imp.setRoi(lefthalf);
                }
                ImageProcessor ips=imp.getProcessor().crop();//normaly it is 16bit. Don't consider other case for now.
                ips=ips.convertToByte(true);
                leftim.setSlice(i+1);
                ImageProcessor ipl=leftim.getProcessor();
                //red
                FloatProcessor flp=ipl.toFloat(0,null);
                flp.copyBits(ips,0,0,5);//MULTIPLY = 5;
                flp.multiply((1.0/255));
                ipl.setPixels(0,flp);
                //green
                flp=ipl.toFloat(1,null);
                flp.copyBits(ips,0,0,5);//MULTIPLY = 5;
                flp.multiply((1.0/255));
                ipl.setPixels(1,flp);
                //blue
                flp=ipl.toFloat(2,null);
                flp.copyBits(ips,0,0,5);//MULTIPLY = 5;
                flp.multiply((1.0/255));
                ipl.setPixels(2,flp);
                //IJ.log(String.valueOf(i));
            }
        }
        else if(lable.equals("Replot"))
        {
            if(xindex==null)
            {
                return;
            }
            else
            {
                double upperlimit=Double.parseDouble(upperlimittxt.getText());
                double lowerlimit=Double.parseDouble(lowerlimittxt.getText());
                //IJ.log("imp update point? 1");
                plot=new Plot("plot","slicenum","ratio",new double[]{0.0},new double[]{0.0});
                ImageProcessor protip = plotDivideddata(plot, imp.getShortTitle(), lowerlimit, upperlimit, runmedwindow);
                //IJ.log("imp update point? 2");
                //plot.show();
                //IJ.log("imp update point? 3");
                plotimp=new ImagePlus(imp.getShortTitle(),protip);
                //IJ.log("imp update point? 4");
                plotimp.show();
                prefs.put("UPPER", String.valueOf(upperlimit)); //save in the preference
                prefs.put("LOWER", String.valueOf(lowerlimit));
                IJ.log("upper "+String.valueOf(upperlimit)+ " lower "+String.valueOf(lowerlimit));
            }
        }//else if(lable.equals("Replot")) end
        else if(lable.equals("Ratio data"))
        {
            if(xindex==null)
            {
                return;
            }
            String header="";
            for(int i=0;i<(indexes.length);i++)
            {
                    if(i!=backgroundroiindex)
                    {
                        String roiname=roinamearray[indexes[i]];
                        header=header+roiname+"\t";
                    }
            }
            StringBuffer sb = new StringBuffer();
            String v="";
            for(int j=0;j<slicenum;j++)
            {
                for(int i=0;i<(indexes.length);i++)
                {
                    if(i!=backgroundroiindex)
                    {
                    	if(dividebyleft.getState())
                    	{
                    		v=String.valueOf(invertyvalue[i][j])+"\t";
                    	}
                    	else
                    	{
                    		v=String.valueOf(yvalue[i][j])+"\t";                    		
                    	}
                        sb.append(v);
                    }
                }
                sb.append("\n");
            }
            
            ij.text.TextWindow tw = new ij.text.TextWindow("Ratio data", header, sb.toString(), 300, 600);
        }//else if(lable.equals("Ratio data")) end
        else if(lable.equals("Abort"))
        {
        	if(dc!=null&&dc.isAlive())
        	{
        		IJ.log("dc is alive");
        		//dc.interrupt();
        		abortflag=true;
        	}
        }//else if(lable.equals("Abort")) end
    }
    
    /*public ImagePlus backgroundSubtructImage(Roi roi)
    {
        imp.setRoi(roi);
        return;
        
    }*/
    
    ////////////////////////////////////////////////////////////////////////////////////////
    public void startTrace(){
        prepImageinfo();
        posarray=new double[slicenum][3];
        //////////////////////////////////// data collection part
        if(!searchboth.getState())
        {
            //get data by searching just half of image's center. For samples those have relatively small movement.
            output=getDataBysearchHalf(ip, imp);
        }
        else
        {
            //get data by searching both left and right center. For samples those have large movement.
            output=getDataBysearchBoth(ip, imp);
        }
        if(output==null)
        {
        	IJ.log("no output");
        	return;
        }
        //////////////////////////////////// data output part
        //Prepare string to save data into txt file
        String strforsave;
        String header="";
        String BR = System.getProperty("line.separator");
        //header preparation
        //1st line has rois width height
        for(int i=0; i<indexes.length;i++)
        {
            String roiname=roinamearray[indexes[i]];
            
            header=header+roiname+","+roiswidthheight[i][0]+","+roiswidthheight[i][1]+",";
        }
        header=header+BR;
        //2nd line
        header=header+"time,";//first column is time point.
        header=header+"xpos,ypos,zpos"+",";//xyz position
        for(int i=0; i<(indexes.length)*2;i++)
        {
            String roiname;
            if(i<(indexes.length))
                roiname="l_"+roinamearray[indexes[i]];
            else
                roiname="r_"+roinamearray[indexes[i-(indexes.length)]];
            header=header+roiname+"_x,"+roiname+"_y,"+roiname+"_mean,";
        }
        IJ.log(header);
        strforsave=header+BR;
        StringBuffer strbuff=new StringBuffer();
        String aslicestring="";
        //actual data
        for(int j=0;j<slicenum;j++)
        {
            aslicestring="";
            aslicestring=String.valueOf(frameinterval*j)+",";//time
            aslicestring=aslicestring+String.valueOf(posarray[j][0])+","+String.valueOf(posarray[j][1])+","+String.valueOf(posarray[j][2])+",";
            for(int i=0;i<(indexes.length)*3*2;i++)//there are left right data, so multiply 2
            {
                aslicestring=aslicestring+String.valueOf(output[j][i])+",";
            }
            //IJ.log(aslicestring);
            strbuff.append(aslicestring+BR);
            //strforsave=strforsave+aslicestring+BR;
        }
        strforsave=strforsave+strbuff.toString();
        String defdir=IJ.getDirectory("image");
        String shorttitle=imp.getShortTitle();
        IJ.log("Output is saved in; "+defdir);
        IJ.saveString(strforsave,defdir+shorttitle+".txt");//save data into same dir name as imagetitle.txt
        
        //Jmalyze compatible format
        if(jmalzecompatible.getState())
        {
            //Prepare area for Jmalyze compatible format
            String jmstr="";
            double[] areas= new double[indexes.length];
            for(int i=0;i<indexes.length;i++)
            {
                Roi temproi=(Roi) Rois.get(Roilist.getItem(indexes[i]));
                imp.setRoi(temproi);
                imstat=imp.getStatistics(1);//area 1
                areas[i]=imstat.area;
                //IJ.log("area#"+i+"; "+String.valueOf(areas[i]));
            }
            //if(true)return;
            for(int j=0;j<slicenum;j++)
            {
                //String aslicestring="";
                aslicestring="";
                aslicestring=String.valueOf(frameinterval*j)+" "
                                +String.valueOf(output[j][backgroundroiindex*3+2])+" "
                                +String.valueOf(output[j][(backgroundroiindex+indexes.length)*3+2])+" ";
                for(int i=0;i<indexes.length;i++)
                {
                    if(i!=backgroundroiindex)
                    {
                        aslicestring=aslicestring
                                        +String.valueOf(output[j][i*3])+" "
                                        +String.valueOf(output[j][i*3+1])+" "
                                        +areas[i]+" "
                                        +String.valueOf((output[j][i*3+2]-output[j][backgroundroiindex*3+2])*areas[i])+" ";//(intensity-backgound)*area
                    }
                }
                for(int i=0;i<indexes.length;i++)//right
                {
                    if(i!=backgroundroiindex)
                    {
                        aslicestring=aslicestring
                                        +String.valueOf(output[j][(i+indexes.length)*3])+" "
                                        +String.valueOf(output[j][(i+indexes.length)*3+1])+" "
                                        +areas[i]+" "
                                        +String.valueOf((output[j][(i+indexes.length)*3+2]-output[j][(backgroundroiindex+indexes.length)*3+2])*areas[i])+" ";
                    }
                }
                //IJ.log(aslicestring);
                jmstr=jmstr+aslicestring+BR;
            }
            IJ.saveString(jmstr,defdir+shorttitle+".log");//save jmalyze compatible data as imagetitle.log
        }
        
        ////////////////////////////////////
        ////////draw a plot
        xindex=new double[slicenum];
        yvalue=new double[indexes.length][slicenum];
        invertyvalue=new double[indexes.length][slicenum];
        double maxval=0;
        double minval=0;//temporally enter zero.
        for(int i=0;i<indexes.length;i++)//if the first roi is background, it's NaN. so need check all/other roi ratio.
        {
            //output[slicenum][roiindex]  output[0][2] wrong? must be[0][i*3+2] and [0][i*3+2+(indexes.length)*3]? 
            // (left_#i_roi-left_bg_roi)/(right_#i_roi-rightt_bg_roi) is the roi is bg, 0/0 NaN
            double candidatemin=(output[0][i*3+2]-output[0][(indexes[backgroundroiindex])*3+2])
            /(output[0][(i*3+(indexes.length)*3)+2]-output[0][(indexes[backgroundroiindex]+indexes.length)*3+2]);
            //IJ.log("minval "+String.valueOf(minval));
            //IJ.log("candidatemin "+String.valueOf(candidatemin));
            if(candidatemin==candidatemin)//double==Double.NaN always returen false, background gives NaN(=0/0)
                minval=candidatemin;//if not NaN, temporally enter candidatemin
        }
        for(int j=0; j<slicenum;j++)//calculating ratio
        {
            xindex[j]=j+1;
            for(int i=0;i<(indexes.length);i++)
            {
                double leftsub=output[j][(i*3)+2]-output[j][(indexes[backgroundroiindex])*3+2];//background subtracted left value.
                double rightsub=output[j][((i+indexes.length)*3)+2]-output[j][(indexes[backgroundroiindex]+indexes.length)*3+2];
                //IJ.log(String.valueOf(leftsub)+" "+String.valueOf(rightsub));
                //if(dividebyleft.getState())
                //{
                    yvalue[i][j]=leftsub/rightsub;
                //}
                //else
                //{
                    invertyvalue[i][j]=rightsub/leftsub;
                //}
                if(yvalue[i][j]>maxval)
                    maxval=yvalue[i][j];
                if(yvalue[i][j]<minval)
                    minval=yvalue[i][j];
            }
        }
	IJ.log("minval "+String.valueOf(minval));
	IJ.log("maxval "+String.valueOf(maxval));
        if(dividebyleft.getState())
        {
        	double tempmax=maxval;
        	double tempmin=minval;
        	maxval=1/tempmin;
        	minval=1/tempmax;
        }
        plot=new Plot("plot","slicenum","ratio",new double[]{0.0},new double[]{0.0});
        ImageProcessor protip = plotDivideddata(plot,shorttitle, minval, maxval, runmedwindow);
        //save the plot as png file
        //ImageProcessor protip=plot.getProcessor();
        //plot.show();
        plotimp=new ImagePlus(shorttitle,protip);
        plotimp.show();
        FileSaver filesave=new FileSaver(plotimp);
        filesave.saveAsPng(defdir+shorttitle+".png");
    }
    
    /////////////////////////////////////////////////////////////////////////////////////////////////////////////
    public ImageProcessor plotDivideddata(Plot plot_, String shorttitle, double min, double max)
    {
        return plotDivideddata(plot_, shorttitle, min, max, 0);
    }
    
    /////////////////////////////////////////////////////////////////////////////////////////////////////////////
    //for runmed filtered plot filterwidth must be even
    public ImageProcessor plotDivideddata(Plot plot_, String shorttitle, double min, double max, int filterwidth)
    {
    	//IJ.log("new plot function with runmed filter "+String.valueOf(filterwidth));
    	//these are reused at slice indicater
    	plottedmin=min;
    	plottedmax=max;
	double[][] plottingyvalue=new double[indexes.length][slicenum];
	if(dividebyleft.getState())
	{
		plottingyvalue=invertyvalue;
	}
	else
	{
		plottingyvalue=yvalue;
	}
	//double[] minandmaxarray;
	    if(filterwidth!=0 && filteredyval==null)
	    {
	    	//IJ.log("if(filterwidth!=0 && filteredyval==null)");
	    	xindex_filtered = new double[slicenum-filterwidth+1];
	    	filteredyval = new double[indexes.length][slicenum-filterwidth+1];
		//minandmaxarray = new double[indexes.length*2];
	        for(int i=0;i<(indexes.length);i++)
        	{
        	        if(i!=backgroundroiindex)
	                {
				//IJ.log("invertyvalue "+String.valueOf(invertyvalue[i][i]));
				double[] temparray = runMed(plottingyvalue[i], filterwidth, true);
				//cut out circular parts
				for(int j=0; j<filteredyval[i].length;j++)
				{
					//IJ.log("temparray[j+filterwidth/2]"+ String.valueOf(temparray[j+filterwidth/2]));
					filteredyval[i][j]=temparray[j+filterwidth/2];
					//IJ.log("filteredyval[i][j] "+ String.valueOf(filteredyval[i][j]));
				}
				//IJ.log("filteredyval "+String.valueOf(filteredyval[i][i]));
				//IJ.log(String.valueOf(filteredyval[i].length));
				//double[] minandmax=range(plottingyvalue[i]);
				//minandmaxarray[i*2]=minandmax[0];
				//minandmaxarray[i*2+1]=minandmax[1];
			}
		}
		/*
		if(plottedmin==0 && plottedmax==0)
		{
			double minandmax[]=range(minandmaxarray);
	    		plottedmin=minandmax[0];
	    		plottedmax=minandmax[1];
		}
		*/
        	for(int j=0; j<slicenum-filterwidth+1;j++)//calculating ratio
        	{
            		xindex_filtered[j]=j+1+filterwidth/2;
	    	}
	    }
        //Plot plot=new Plot("plot","slicenum","ratio",xindex,yvalue[0]);
        
        plot_.setLimits(0,slicenum,plottedmin,plottedmax);
        Color col;
        int serial=0;
	//plot raw data
	for(int i=0;i<(indexes.length);i++)
        {
		//IJ.log("i "+String.valueOf(i) +" "+ Roilist.getItem(indexes[i]));
            if(i!=backgroundroiindex)
            {
                //change color brightness by even/odd. alpha seems not work for lines but work with lable
                col= Color.getHSBColor((float)((serial*30)%100/100.0), (float)1.0, (float)(1.0-(serial%2)*0.3)); 
		if(filterwidth!=0)
		{
	                col= Color.getHSBColor((float)((serial*30)%100/100.0), (float)0.3, (float)(1.0-(serial%2)*0.3)); 
		}
		plot_.setColor(col);
		plot_.addPoints(xindex,plottingyvalue[i],2);
		if(filterwidth==0)
		{
                	plot_.addLabel(0.8+(0.05*(serial/5)),(serial%5)*0.1,roinamearray[i]); 
		}
                serial++;
	     }
	}
	//plot filtered data
	if(filterwidth!=0)
	{
        	serial=0;
        	for(int i=0;i<(indexes.length);i++)
        	{
		//IJ.log("i "+String.valueOf(i) +" "+ Roilist.getItem(indexes[i]));
            		if(i!=backgroundroiindex)
            		{
				col= Color.getHSBColor((float)((serial*30)%100/100.0), (float)1.0, (float)(1.0-(serial%2)*0.3)); 
                		plot_.setColor(col);
				//IJ.log("addingpoints "+String.valueOf(filteredyval[i][0]));
                    		plot_.addPoints(xindex_filtered,filteredyval[i],2);//int value determin shape. dot 6;circel 0; cross 5;line 2;triangle 4; x 1; box 3
		                plot_.addLabel(0.8+(0.05*(serial/5)),(serial%5)*0.1,roinamearray[i]);                
                		serial++;
			}
                }
        }
        plot_.setColor(Color.black);
        plot_.addLabel(0,1,shorttitle);
    	//IJ.log("new plot function end");
        return plot_.getProcessor();
    }
    //public ImageProcessor plotDivideddata(Plot plot_, String shorttitle, double min, double max, int filterwidth) end
    
	//range
	double[] range(double[] vector)
	{
		double min=vector[0];
		double max=vector[0];
		for(int i=1; i<vector.length;i++)
		{
			if(min>vector[i])
				min=vector[i];
			if(max<vector[i])
				max=vector[i];
		}
		return new double[]{min, max};
	}
    //running median
    //not implemented yet circ==false
    double[] runMed(double[] array, int window, boolean circ)
    {
        double[] returnval=new double[array.length];
        //System.arraycopy(vector, i, temparray,0,window);
        if(circ)
        {
        	double[] temparray=new double[window];
        	for(int i=0;i<array.length;i++)
        	{
        		for(int j=0;j<window;j++)
        		{
        			temparray[j]=array[(array.length+i-window/2+j)%array.length];
        		}
        		returnval[i]=median(temparray);
        	}
        }
	//cut out circular parts method. by using another loop
	/*
	double[] temparray = new double[array.length];
	double[] returnval new double[array.length-filterwidth+1];
	temparray=runMed(array, window, circ);
	for(int i=0; i<returnval.length;i++)
	{
		returnval[i]=temparray[i+filterwidth/2];
	}
	*/
        else
        {
        	for(int i=0;i<array.length;i++)
        	{
        		double sumoflocal=0;
        		//int denominator=window*2+1;
        		int denominator=window;
        		double[] tempvec=new double[window];
        		for(int k=-(window/2+1);k<=window/2+1;k++)
        		{
        			if(i+k<0)
        			{
        			}
        			else if (i+k>=array.length)
        			{
        			}
        			else
        			{

        			}

        		}
        		//returnval[i]=
        	}
        }
    	return returnval;	
    }
    
    double[] runMed(double[] array, int window)
    {
        return runMed(array, window, false);
    }
    
    //median
    double median(double[] vector)
    {
        double[] temparray=new double [vector.length];//To do deep copy, make new instance.
        for(int i=0; i<vector.length;i++)
        {
            temparray[i]=vector[i];
        }
        java.util.Arrays.sort(temparray);
        int middle=temparray.length/2;
        return temparray[middle];
    }

    /////////////////////////////////////////////////////////////////////////////////////////////////////////////
    //added ver10 extract xyz stage position data from meta data
    public double[] getSlicepos()
    {
    //check if the image has xyzpos data in Fileinfo.info field as "xpos="+String.valueOf(xposarray[i])+",ypos="+String.valueOf(yposarray[i])+",zpos="+String.valueOf(zpos);
        //not Fileinfo.info, seems stack.property imp.property? don't understand how info.info turns into lable of slice. but,
        //stack.getSliceLabels(); does work with stack but not with virtual stack use getSliceLabel to get each data.
        
        double[] asliceposarray=new double[] {0,0,0};//xyz
        ImageStack stack = imp.getStack();
        String label = stack.getSliceLabel(imp.getCurrentSlice());
        IJ.log(label);
        
        if(label!=null)
        {
            IJ.log("label info 1st slice; " + label);
            String[] infoarray=label.split("\n|,");//split by \n. stack has original tiff name at 1st line.(virtual stack dont have)
            //May need use BR or something
            for(int i=0;i<infoarray.length;i++)
            {
                if(infoarray[i].indexOf("=")>0)//if this contains =, which means x,y,zpos, not xxxx.tif.
                {
                    String key_=infoarray[i].split("=")[0];
                    double value=Double.parseDouble(infoarray[i].split("=")[1]);
                    IJ.log(" key "+ key_+" value "+String.valueOf(value));
                    if(key_.equals("xpos"))
                    {
                        asliceposarray[0]=value;
                    }
                    else if(key_.equals("ypos"))
                    {
                        asliceposarray[1]=value;
                    }
                    else if(key_.equals("zpos"))
                    {
                        asliceposarray[2]=value;
                    }
                }
            }
        }
        else
        {
            IJ.log("info null");
        }
        
        IJ.log(String.valueOf(asliceposarray[0])+String.valueOf(asliceposarray[1])+String.valueOf(asliceposarray[2]));
        
        return asliceposarray;
    }
    
    public void prepImageinfo(){
        
        //////// Roimanager mustbe opened before run this plugin
        if(Manager.getInstance()==null)
        {
            IJ.showMessage("Need ROI manager containig rois.");
            return;
            //Manager = new RoiManager ();
        }
        else
        {
            Manager=Manager.getInstance();
        }
        Roilist=Manager.getList();
        Rois=Manager.getROIs();
	
	//clear overlay if exist
	Overlay overlay= new Overlay();
	if(imp.getOverlay()!=null)
	{
		overlay=imp.getOverlay();
	}
	overlay.clear();
        
        //////// preparing image infomation
        width=imp.getWidth();
        height=imp.getHeight();
        slicenum=imp.getImageStackSize();
        Calibration calib=imp.getCalibration();
        frameinterval =calib.frameInterval;
        IJ.log(String.valueOf(frameinterval));
        IJ.log(calib.getTimeUnit());
        IJ.log("slicenum:"+slicenum);
        // Ask user to input frameinterval if its 0.0
        if(frameinterval==0.0)
        {
            frameinterval=100;
            GenericDialog gd = new GenericDialog(imp.getTitle());
            gd.addNumericField("Frame interval (msec):", frameinterval, 0);
            gd.showDialog();
            frameinterval=(int)gd.getNextNumber();
            calib.frameInterval=frameinterval;
        }
        IJ.log(String.valueOf(frameinterval));
        //////// making  roi list.
        indexes=new int[Roilist.getItemCount()];
        for(int i=0; i<Roilist.getItemCount();i++)
        {
            indexes[i]=i;
        }
        
        //reserve inital coordinates of Rois. and prepare name of rois
        reserveInitialcoordinates();
        
        
        //////// chech if there is background and fixed , bind roi.
        backgroundroiindex=-1;
        isfixed=new boolean[indexes.length];
        isbind=new boolean[indexes.length];
        isrot=new boolean[indexes.length];
        isref=new boolean[indexes.length];
        bindinfo=new int[indexes.length][3];//[parentroiindex, xshift,yshift]
        rotinfo=new double[indexes.length][3];//[parentroiindex, phi,distance]
        parentrotinfo=new double[slicenum+1][indexes.length][3];//slicenumber and index have same number (index has #0)
        refinfo=new int[indexes.length][3];//[parentroi index,xshift from parent,yshift from parent]
        initialrefinfo=new int[indexes.length][3];
        for(int i=0; i<indexes.length;i++)
        {
            Roi temproiforname=(Roi) Rois.get(Roilist.getItem(i));
            String roinamewithsuffix= temproiforname.getName();
            String roinamesplitted[]=roinamewithsuffix.split("\\.");//ex bg.fx
            IJ.log(String.valueOf(roinamesplitted.length));
            //roinamearray[i]=roinamesplitted[0];
            IJ.log(temproiforname.getName());
            if(roinamesplitted[0].equalsIgnoreCase("bg"))
                backgroundroiindex=i;
            if(roinamesplitted.length>1)
            {
                if(roinamesplitted[1].equalsIgnoreCase("fx"))//fixed roi must have .fx suffix
                    isfixed[i]=true;
                else
                    isfixed[i]=false;
                //////bind roi
                if(roinamesplitted[1].startsWith("bind("))// roi that need to be keep same distance with paticular roi. .bind(parentroiname)
                {
                    
                    isbind[i]=true;
                    String[] parentroiname=roinamesplitted[1].split("[\\(\\)]");//split the .bind(roiname) with ( and ). get roi name.
                    IJ.log(parentroiname[1]);
                    for(int k=0;k<indexes.length;k++)
                    {
                        if(parentroiname[1].equals(roinamearray[k]))
                        {
                            bindinfo[i][0]=k;//parent roi index
                            bindinfo[i][1]=initialcoordinates[i][0]-initialcoordinates[k][0];//x shift
                            bindinfo[i][2]=initialcoordinates[i][1]-initialcoordinates[k][1];//y shift
                        }
                    }
                    IJ.log("shift from parent x "+bindinfo[i][1]+"y "+bindinfo[i][2]);
                }
                else
                    isbind[i]=false;
                //////rotation roi
                if(roinamesplitted[1].startsWith("rot("))// roi that need to be keep same rotation and distance with paticular roi. .rot(parentroiname)
                {
                    
                    isrot[i]=true;
                    String[] parentroiname=roinamesplitted[1].split("[\\(\\)]");//split the .bind(roiname) with ( and ). get roi name.
                    IJ.log(parentroiname[1]);
                    for(int k=0;k<indexes.length;k++)
                    {
                        if(parentroiname[1].equals(roinamearray[k]))
                        {
                            rotinfo[i][0]=k;//parent roi index
                            //detect longitudinal axis of parent
                            double[] parentdata;
                            //if the axis and centroid of parent roi had measued, dont measure again
                            if(parentrotinfo[0][k][0]==0)//initial value must be 0.0. NaN should be better, but... needs more code.
                            {
                                Roi parentroi=(Roi) Rois.get(Roilist.getItem(k));
                                parentdata=detectAxis(ip, imp, parentroi);//parentdata=[xcentroid,ycentroid,maxtheta]
                                IJ.log(String.valueOf(parentdata[0])+","+String.valueOf(parentdata[1])+","+String.valueOf(parentdata[2]));
                                parentrotinfo[0][k]=parentdata;
                            }
                            else 
                            {
                                parentdata=parentrotinfo[0][k];
                            }
                            //if(true) return;
                            
                            imp.setRoi(temproiforname);
                            imstat=imp.getStatistics(32);
                            double xcenter=imstat.xCentroid;
                            double ycenter=imstat.yCentroid;
                            double dx=xcenter-parentdata[0];
                            double dy=ycenter-parentdata[1];
                            double initialrot=Math.atan2(dy,dx);//arc tangent
                            IJ.log("initalrot:"+initialrot/Math.PI*180);
                            rotinfo[i][1]=Math.sqrt(dx * dx + dy * dy);//distance between parent and child
                            rotinfo[i][2]=parentdata[2]-initialrot;
                        }
                    }
                    IJ.log("distance from parent x "+rotinfo[i][1]+"rotate "+rotinfo[i][2]/Math.PI*180);
                }
                else
                    isrot[i]=false;
                //////rotation roi
                if(roinamesplitted[1].startsWith("ref("))// roi that initially locate using reference roi.
                {
                    isref[i]=true;
                    String[] parentroiname=roinamesplitted[1].split("[\\(\\)]");//split the .bind(roiname) with ( and ). get roi name.
                    IJ.log(parentroiname[1]);
                    for(int k=0;k<indexes.length;k++)
                    {
                        if(parentroiname[1].equals(roinamearray[k]))
                        {
                            refinfo[i][0]=k;//parent roi index
                            refinfo[i][1]=initialcoordinates[i][0]-initialcoordinates[k][0];//x shift child-parent
                            refinfo[i][2]=initialcoordinates[i][1]-initialcoordinates[k][1];//y shift
                            int[] temparray= {refinfo[i][0], refinfo[i][1], refinfo[i][2]};//To do deep copy, make new instance.
                            initialrefinfo[i]=temparray;
                        }
                    }
                    IJ.log("refer parent roi, #"+refinfo[i][0]+". shift from parent x "+refinfo[i][1]+"y "+refinfo[i][2]);
                }
                else
                    isref[i]=false;
            }
            else
            {
                isfixed[i]=false;
                isbind[i]=false;
                isrot[i]=false;
            }
        }
        IJ.log(Arrays.toString(isfixed));
        IJ.log(Arrays.toString(isbind));
        
        
        ImageCanvas ic=imp.getCanvas();
        ic.setShowAllROIs(true);//Show all Rois.
        //if(true) return;
        
        //////// logic in the case of no background roi.
        IJ.log(String.valueOf(backgroundroiindex));
        if(backgroundroiindex== -1)
        {
            IJ.showMessage("There is no designated background ROI. Mean of half part of image wiill be used as background");
            //Roi halfofimageroi=new Roi(0,0,width/2,height);
            Roi halfofimageroi;
		if(rightasref.getState())
		{
			halfofimageroi=new Roi(width/2,0,width/2,height);
	    	}
	    	else
	    	{
	    		halfofimageroi=new Roi(0,0,width/2,height);
	    	}
	    
            Manager.add(imp,halfofimageroi,-1);
            Manager.select(Manager.getCount()-1);
            Manager.runCommand("Rename","bg.fx");
            //adding this roi informations......
            Roilist=Manager.getList();
            Rois=Manager.getROIs();
            indexes=new int[Roilist.getItemCount()];
            for(int i=0; i<Roilist.getItemCount();i++)
            {
                indexes[i]=i;
            }
            reserveInitialcoordinates();//initial coorinates and roiname array.
            backgroundroiindex=Manager.getCount()-1;
            //This part need because array can not change size easily
            boolean[] tempisfixed=new boolean[indexes.length];
            boolean[] tempisbind=new boolean[indexes.length];
            boolean[] tempisrot=new boolean[indexes.length];
            boolean[] tempisref=new boolean[indexes.length];
            for(int i=0;i<indexes.length-1;i++)
            {
                tempisfixed[i]=isfixed[i];
                tempisbind[i]=isbind[i];
                tempisrot[i]=isrot[i];
                tempisref[i]=isref[i];
            }
            isfixed=tempisfixed;
            isbind=tempisbind;
            isrot=tempisrot;
            isref=tempisref;
            isfixed[backgroundroiindex]=true;
            isbind[backgroundroiindex]=false;
            isrot[backgroundroiindex]=false;
            isref[backgroundroiindex]=false;
        }
    }
    
    ////////////////////////reserve inital coordinates of Rois. and prepare name of rois
    //ver10 also stock width/height
    public void reserveInitialcoordinates(){
        initialcoordinates=new int[indexes.length][2];
        roinamearray = new String [indexes.length];
        roiswidthheight= new int[indexes.length][2];
        for(int i=0;i<indexes.length;i++)
        {
            Roi temproi=(Roi) Rois.get(Roilist.getItem(indexes[i]));
            java.awt.Rectangle boundary=temproi.getBounds();
            initialcoordinates[i][0]=boundary.x;
            initialcoordinates[i][1]=boundary.y;
            roiswidthheight[i][0]=boundary.width;
            roiswidthheight[i][1]=boundary.height;
            
            String roinamewithsuffix= temproi.getName();
            String roinamesplitted[]=roinamewithsuffix.split("\\.");//ex bg.fx Just put name of roi here. use the name array later 
            roinamearray[i]=roinamesplitted[0];
        }
    }
    
    
    //////////////////////// restore position of Rois
    public void restoreRoipositions(){
        for(int i=0;i<Manager.getCount();i++)
        {
            Roi temproi=(Roi) Rois.get(Roilist.getItem(indexes[i]));
            temproi.setLocation(initialcoordinates[i][0],initialcoordinates[i][1]);
        }
    }
    
    
    
    /////////////////////////////////////////////////correct data by search both center method
    public double[][] getDataBysearchBoth(ImageProcessor ip, ImagePlus imp){
        double[][] returndata=new double [slicenum][(indexes.length*3)*2];
        for(int j=0;j<slicenum;j++)
        {
            imp.setSlice(j+1);
            posarray[j] = getSlicepos();
            double[] leftdata=measureMeanofRois(ip, imp, 0,0);
            double[] rightdata=measureMeanofRois(ip, imp, (int)width/2,0);
            for(int i=0;i<indexes.length;i++)
            {
                //left
                returndata[j][i*3]=leftdata[i*3];//x
                returndata[j][i*3+1]=leftdata[i*3+1];//y
                returndata[j][i*3+2]=leftdata[i*3+2];//mean
                //right
                returndata[j][i*3+(indexes.length)*3]=rightdata[i*3];
                returndata[j][i*3+1+(indexes.length)*3]=rightdata[i*3+1];
                returndata[j][i*3+2+(indexes.length)*3]=rightdata[i*3+2];
                // set moved roi to new position
                temproi=(Roi) Rois.get(Roilist.getItem(indexes[i]));
                java.awt.Rectangle boundary;
                boundary=temproi.getBounds();
                temproi.setLocation((int)leftdata[i*3],(int)leftdata[i*3+1]);
            }
        }
        return returndata;
    }
    
    
    
    
    
    /////////////////////////////////////////////////correct data by search only half center method
    public double[][] getDataBysearchHalf(ImageProcessor ip, ImagePlus imp){
    	//using right half as image to search roi centor
	if(rightasref.getState())
	{
		
	}
    	//////// in the case that LR shift was assigned by manually      
        if(fixedshift.getState())
        {
        	int assingedx;
		if(rightasref.getState())
		{
			assingedx=Integer.parseInt(assignedxshifttxt.getText())-(int)width/2;
		}
		else
		{
			assingedx=Integer.parseInt(assignedxshifttxt.getText())+(int)width/2;
        	}
		int assingedy=Integer.parseInt(assignedyshifttxt.getText());
        	averagelrshift=new double[] {assingedx,assingedy};
        	
	        avelrshiftofeachrois=new int[indexes.length][2];
            for(int i=0;i<indexes.length;i++)
            {
                avelrshiftofeachrois[i]=new int[] {assingedx,assingedy};
            }
        	//if the background roi is half of image, may need to not shift it?
        	//or treated as so? see measureMeanofRois ... later
            Roi bgroi=(Roi) Rois.get(Roilist.getItem(backgroundroiindex));
            Roi halfofimageroi;
		if(rightasref.getState())
		{
			halfofimageroi=new Roi(width/2,0,width/2,height);
		}
		else
		{
			halfofimageroi=new Roi(0,0,width/2,height);
		}
            if(bgroi.equals(halfofimageroi))
            {
            	IJ.log("bg roi is half of it");
            	//abortflag=true;
		if(rightasref.getState())
		{
            		avelrshiftofeachrois[backgroundroiindex]= new int[] {(int) -width/2,0};
		}
		else
		{
            		avelrshiftofeachrois[backgroundroiindex]= new int[] {(int)width/2,0};
		}
            }
        }
        else
        {
	        //////// detecting LR shift of each roi automatically for later use.
	        int[][] leftlocations;
	        int[][] rightlocations;
	        int[][][] lrshift=new int[refslicenum][indexes.length][2];//initial x slices are used for measuring average lr shift
	        for(int j=0;j<refslicenum;j++)
	        {
	            imp.setSlice(j+1);
	            double[] lefttempstrage =new double[(int)(indexes.length)*3];
	            lefttempstrage=measureMeanofRois(ip,imp,0,0);
	            double[] righttempstrage =new double[(int)(indexes.length)*3];
	            righttempstrage=measureMeanofRois(ip,imp,(int)width/2,0);
	            for(int i=0;i<indexes.length;i++)
	            {
	                IJ.log("righttempstrage x; "+righttempstrage[i*3]);
	                lrshift[j][i][0]=(int)(righttempstrage[i*3]-lefttempstrage[i*3]);//x
	                lrshift[j][i][1]=(int)(righttempstrage[i*3+1]-lefttempstrage[i*3+1]);//y
	                // set moved roi to new position
	                temproi=(Roi) Rois.get(Roilist.getItem(indexes[i]));
	                java.awt.Rectangle boundary;
	                boundary=temproi.getBounds();
	                temproi.setLocation((int)lefttempstrage[i*3],(int)lefttempstrage[i*3+1]);
	            }
	            
	            for(int i=0;i<indexes.length;i++)// checking
	                IJ.log("Nun"+i+"xshift; "+String.valueOf(lrshift[j][i][0])+" yshift;"+String.valueOf(lrshift[j][i][1]));
	        }
	        //if(true) return;
	        avelrshiftofeachrois=new int[indexes.length][2];
	        averagelrshift=new double[] {0,0};//average of average shift of each roi. It means shift of whole picture.
	        int nonfixednum=0;
	        for(int i=0;i<indexes.length;i++)
	        {
	            double xsum=0;
	            double ysum=0;
	            for(int j=0; j<refslicenum; j++)
	            {
	                xsum=xsum+lrshift[j][i][0];
	                ysum=ysum+lrshift[j][i][1];
	            }
	            avelrshiftofeachrois[i][0]=(int)Math.round(xsum/refslicenum);
	            avelrshiftofeachrois[i][1]=(int)Math.round(ysum/refslicenum);
	            if(!isfixed[i]&&!isbind[i]&&!isrot[i])//To calculate general shift, eliminate fixed and bind roi data
	            {
	                averagelrshift[0]=(double)averagelrshift[0]+avelrshiftofeachrois[i][0];
	                averagelrshift[1]=(double)averagelrshift[1]+avelrshiftofeachrois[i][1];
	                nonfixednum++;
	            }
	        }
	        for(int i=0;i<indexes.length;i++)// checking
	            IJ.log("Nun"+i+"ave xshift; "+String.valueOf(avelrshiftofeachrois[i][0])+"ave yshift;"+String.valueOf(avelrshiftofeachrois[i][1]));
	        averagelrshift[0]=averagelrshift[0]/nonfixednum;
	        averagelrshift[1]=averagelrshift[1]/nonfixednum;
	        IJ.log("averagelrshift x; "+Math.round(averagelrshift[0])+"averagelrshift y; "+Math.round(averagelrshift[1]));
	        //if(true) return;
	        
	        //restore position of Rois
	        restoreRoipositions();
	        //also reset refinfo
	        for(int i=0; i<indexes.length;i++)
	        {
	            int[] temparray= {initialrefinfo[i][0], initialrefinfo[i][1], initialrefinfo[i][2]};//To do deep copy, make new instance.
	            refinfo[i]=temparray;
	        }
        }
        //////////////////////////////////////  Here is main part of this method/////////////////////////////////////////////////
        //output valiable left rois x,y,mean and right rois x,y,mean for each slice
        //ex; leftroi1x,leftroi1y,leftroi1mean,leftroi2x,leftroi2y,leftroi2mean,rightroi1x,rightroi1y,rightroi1mean,rightroi2x,rightroi2y,rightroi2mean.
        // In this method, center of math of left part are sought first, and averagelrshift value of each rois are used to position the roi at right part.
        // NOT the case. averagelrshift is not used yet. need implement future.
        
        double[][] returndata=new double [slicenum][(indexes.length*3)*2];
        for(int j=0;j<slicenum;j++)
        {
        	if(abortflag==true)
        	{
        		IJ.log("abort ");
        		abortflag=false;
        		//need any clean up process?
        		return null;
        		//new double[][] {{0.0},{0.0}};
        	}
            imp.setSlice(j+1);
            posarray[j] = getSlicepos();
            //double[] leftdata=measureMeanofRois(ip, imp, 0,0);
            double[] dataatrefimage=measureMeanofRois(ip, imp, 0,0);
	    
	    //double[] rightdata=new double[(indexes.length*3)];
            for(int i=0;i<indexes.length;i++)
            {
                // set roi to non-ref part (normally right half image)
                temproi=(Roi) Rois.get(Roilist.getItem(indexes[i]));
                java.awt.Rectangle boundary;
                boundary=temproi.getBounds();
                temproi.setLocation((int)(dataatrefimage[i*3]+avelrshiftofeachrois[i][0]),(int)(dataatrefimage[i*3+1]+avelrshiftofeachrois[i][1]));//shift to non-ref part using average shift value.
                imp.setRoi(temproi);
                imstat=imp.getStatistics(2);
                //double rightmean=imstat.mean;
                double nonrefmean=imstat.mean;
		//double[] leftdata=new double[(indexes.length*3)];
                // set moved roi to new left position
                temproi.setLocation((int)dataatrefimage[i*3],(int)dataatrefimage[i*3+1]);
                //putting measured data to output valiable
	 	if(rightasref.getState())
		{
                	//left
                	returndata[j][i*3]=dataatrefimage[i*3]+avelrshiftofeachrois[i][0];//x
                	returndata[j][i*3+1]=dataatrefimage[i*3+1]+avelrshiftofeachrois[i][1];//y
                	returndata[j][i*3+2]=nonrefmean;//mean
                	//right
                	returndata[j][i*3+(indexes.length)*3]=dataatrefimage[i*3];
                	returndata[j][i*3+1+(indexes.length)*3]=dataatrefimage[i*3+1];
                	returndata[j][i*3+2+(indexes.length)*3]=dataatrefimage[i*3+2];
                	IJ.log("right mean: "+dataatrefimage[i*3+2]);
		}
		else
		{
                	//left
                	returndata[j][i*3]=dataatrefimage[i*3];//x
                	returndata[j][i*3+1]=dataatrefimage[i*3+1];//y
                	returndata[j][i*3+2]=dataatrefimage[i*3+2];//mean
                	//right
                	returndata[j][i*3+(indexes.length)*3]=dataatrefimage[i*3]+avelrshiftofeachrois[i][0];
                	returndata[j][i*3+1+(indexes.length)*3]=dataatrefimage[i*3+1]+avelrshiftofeachrois[i][1];
                	returndata[j][i*3+2+(indexes.length)*3]=nonrefmean;
                	IJ.log("right mean: "+nonrefmean);
		}
            }
            
        }
        //restore position of Rois
        /*
        for(int i=0;i<Manager.getCount();i++)
        {
            temproi=(Roi) Rois.get(Roilist.getItem(indexes[i]));
            temproi.setLocation(initialcoordinates[i][0],initialcoordinates[i][1]);
        }*/
        imp.updateImage();
        return returndata;
    }
    
    
    
    
    //////////////////////// This method search location where center of the given roi located center of mass. 
    //////// and return a int array containing roi location
    public int[] searchCenter(ImagePlus imp, Roi roi){
        ImageStatistics imstat;
        imp.setRoi(roi);
        
        //prepare 3 arrays, previous_but_one, previous, current.
        java.awt.Rectangle boundary=roi.getBounds();
        //IJ.log("given roi "+boundary.x+" "+ boundary.y);
        int[] previous_but_one={boundary.x, boundary.y};
        int[] previous= new int [previous_but_one.length] ;
        int[] current= new int [previous.length];
        System.arraycopy(previous_but_one, 0, previous,0,previous_but_one.length);// deep copy. supporse to be. NO. shallow. shouldn't work as intended initially. need fix later.
        System.arraycopy(previous, 0, current,0,previous.length);
        for(int i=0;i<20;i++)//limiting repeat to 10 times. just in case.
        {
            System.arraycopy(previous, 0, previous_but_one,0,previous.length);// previous_but_one<-previous
            System.arraycopy(current, 0, previous,0,current.length);//previous<-current
            imstat=imp.getStatistics(64);
            //IJ.log("xcenter "+String.valueOf(imstat.xCenterOfMass));
            current[0]=(int) Math.round(imstat.xCenterOfMass-(boundary.width)/2);
            current[1]=(int) Math.round(imstat.yCenterOfMass-(boundary.height)/2);
            roi.setLocation(current[0],current[1]);
            //IJ.log("x,"+current[0]+"y,"+current[1]);
            imp.setRoi(roi);
            if(Arrays.equals(previous,current))//compare if the new location is same as before. It is possible osscilating at two point
            {
                IJ.log("returned at "+i+"th repeat");
                return current;
            }
            else if(Arrays.equals(previous_but_one,current))// compare with previous but one location.
            {
                IJ.log("returned at "+i+"th repeat at previous but one.");
                return current;
            }
        }
        return current;
    }
    
    
    
    
    
    
    
    
    //////////////////////// Measure mean intensity value and returen the mean as int value;
    //Calling; searchCenter
    public int measureMeanintensity (ImagePlus imp, Roi roi, int index){
        imp.setRoi(roi);
        if(!isfixed[index])// if the roi is NOT fixed one
        {
            int[] newlocation=searchCenter(imp, roi);
            roi.setLocation(newlocation[0],newlocation[1]);//newlocation[0] is x, newlocation[1] is y coordinate.
            IJ.log("x;"+String.valueOf(newlocation[0])+" y;"+String.valueOf(newlocation[1]));
            imp.setRoi(roi);
        }
        
        ImageStatistics stat=imp.getStatistics(2);//MEAN=2    }
        return (int) stat.mean;
    }
    
    
    
    
    
    
    
    
    
    //////////////////////////////// measuring mean of each roi. 
    //Calling; measureMeanintensity, searchCenter, 
    public double[] measureMeanofRois (ImageProcessor ip, ImagePlus imp, int xshift, int yshift){
        //////// setting background value
        //returen x,y,mean array
        double[] returnval=new double[(int)(indexes.length)*3];
        int backgroundvalue;
        if(!isbind[backgroundroiindex])//if background roi is not bind roi
        {
            Roi backgourndroi=(Roi) Rois.get(Roilist.getItem(backgroundroiindex));
            java.awt.Rectangle boundary;
            boundary=backgourndroi.getBounds();
            backgourndroi.setLocation(boundary.x+xshift,boundary.y+yshift);
            backgroundvalue=measureMeanintensity(imp, backgourndroi,backgroundroiindex);//This method can decide if its fixed or not
        }
        else
        //if backgroundroi is bind roi, use mean of the half part to make bg subtracted image. 
        //but this value is used just for prepare center search image. actural background mean value is measured later.
        {
            Roi halfofimageroi=new Roi(xshift,yshift,width/2,height);
            imp.setRoi(halfofimageroi);
            imstat=imp.getStatistics(2);
            backgroundvalue=(int)imstat.mean;
        }
        ImageProcessor ip2 = ip.duplicate();
        
        ip2.add(-backgroundvalue);
        ImagePlus imp2=new ImagePlus("subtracted",ip2);//here is background subtracted image.
        IJ.log("indexes.length "+String.valueOf(indexes.length)+" isbind.length "
        		+String.valueOf(isbind.length)+String.valueOf(isrot.length)+String.valueOf(isref.length));
        
        for(int i=0;i<indexes.length;i++)
        {
            if(!isbind[i]&&!isrot[i]&&!isref[i])//bind, rot and ref roi need other rois position, so process later.
            {
                Roi temproi=(Roi) Rois.get(Roilist.getItem(indexes[i]));
                //Roi temproi=(Roi) locRois.get(Roilist.getItem(indexes[i]));
                imp.setRoi(temproi);
                java.awt.Rectangle boundary;
                boundary=temproi.getBounds();
                if(i!=backgroundroiindex)//background was measured already above
                {
                temproi.setLocation(boundary.x+xshift,boundary.y+yshift);
                    if(!isfixed[i])//if the roi is NOT fixed one
                    {
                        int[] newlocation=searchCenter(imp2, temproi);//pass background subtracted image to searchCenter 
                        temproi.setLocation(newlocation[0],newlocation[1]);
                        IJ.log("x;"+String.valueOf(newlocation[0])+" y;"+String.valueOf(newlocation[1]));
                        imp.setRoi(temproi);
                    }
                    imstat=imp.getStatistics(2);
                    IJ.log("Mean of "+temproi.getName()+" x("+xshift+") y("+yshift+"); "+String.valueOf(imstat.mean));
                    boundary=temproi.getBounds();
                    returnval[i*3]=boundary.x;
                    returnval[i*3+1]=boundary.y;
                    returnval[i*3+2]=imstat.mean;
                }
                else
                {
                    boundary=temproi.getBounds();
                    //IJ.log("background x "+boundary.x);
                    returnval[i*3]=boundary.x;
                    returnval[i*3+1]=boundary.y;
                    returnval[i*3+2]=backgroundvalue;
                }
            //imp2.show();
            }//end if(!isbind)
        }//end for
        
        for(int i=0;i<indexes.length;i++)//bind roi processing part
        {
            if(isbind[i])
            {
                Roi temproi=(Roi) Rois.get(Roilist.getItem(indexes[i]));
                java.awt.Rectangle boundary;
                //bindinfo[i][0] has parent roi index
                temproi.setLocation((int)returnval[(bindinfo[i][0])*3]+bindinfo[i][1],(int)returnval[(bindinfo[i][0])*3+1]+bindinfo[i][2]);
                imp.setRoi(temproi);
                boundary=temproi.getBounds();
                imstat=imp.getStatistics(2);
                returnval[i*3]=boundary.x;
                returnval[i*3+1]=boundary.y;
                returnval[i*3+2]=imstat.mean;
            }
            else if(isref[i])
            {
                //refinfo[i][0] has parent roi index
                Roi temproi=(Roi) Rois.get(Roilist.getItem(indexes[refinfo[i][0]]));
                java.awt.Rectangle boundary;
                boundary=temproi.getBounds();
                int[] parentpos= {boundary.x, boundary.y};
                //crop the refroi
                Roi croproi;
                croproi=new Roi(parentpos[0],parentpos[1],boundary.width,boundary.height);
                imp2.setRoi(croproi);
                ImageProcessor ipcrop=ip2.crop();
                ImagePlus impcrop=new ImagePlus("crop",ipcrop);
                //median filter
                RankFilters rf = new RankFilters();
                //rf.setup("median",imp);
                rf.rank(ipcrop, 0.0, 4);// median 4 periodic black white noize cause miss thresholding, so eliminate those noize
                //interpolate 2x size
                ipcrop.setInterpolationMethod(2);//BICUBIC 2
                ImageProcessor ipcropresize=ipcrop.resize(boundary.width*2);
                ImagePlus impresize=new ImagePlus("resize",ipcropresize);
                //unsharpmask
                FloatProcessor fp= ipcropresize.toFloat(0, null);
                //ip.convertToFloat();
                fp.snapshot();
                UnsharpMask um= new UnsharpMask();
                um.sharpenFloat(fp, (double)4, (float)0.9);
                ipcropresize.setPixels(0, fp);
                //pass prepsocessed image to searchCenter
                temproi=(Roi) Rois.get(Roilist.getItem(indexes[i]));
                boundary=temproi.getBounds();
                //OvalRoi(int x, int y, int width, int height);
                OvalRoi resizedroi= new OvalRoi(refinfo[i][1]*2, refinfo[i][2]*2, boundary.width*2,boundary.height*2);
                //set location at the cropped image. the cropped one has 2x resolution
                //temproi.setLocation(refinfo[i][1]*2, refinfo[i][2]*2);
                //impcrop.setProcessor("crop",ipcrop);
                int[] newlocation=searchCenter(impresize, (Roi) resizedroi);
                temproi.setLocation(parentpos[0]+Math.round(newlocation[0]/2),parentpos[1]+Math.round(newlocation[1]/2));//set location at the original image
                IJ.log(temproi.getName()+" x;"+String.valueOf(parentpos[0]+newlocation[0])+" y;"+String.valueOf(parentpos[1]+newlocation[1]));
                /*
                //locate initial pos using ref roi
                temproi.setLocation(parentpos[0]+refinfo[i][1], parentpos[1]+refinfo[i][2]);
                IJ.log("setloc at "+String.valueOf(parentpos[0]+refinfo[i][1])+" "+String.valueOf(parentpos[1]+refinfo[i][2]));
                int[] newlocation=searchCenter(imp2, temproi);//pass background subtracted image to searchCenter 
                temproi.setLocation(newlocation[0],newlocation[1]);
                
                */
                //impresize.show();
                //if(true)return null;
                imp.setRoi(temproi);
                boundary=temproi.getBounds();
                imstat=imp.getStatistics(2);
                returnval[i*3]=boundary.x;
                returnval[i*3+1]=boundary.y;
                returnval[i*3+2]=imstat.mean;
                //update refinfo
                refinfo[i][1]=boundary.x-parentpos[0];//x
                refinfo[i][2]=boundary.y-parentpos[1];//y
                IJ.log("shift from, x;"+String.valueOf(refinfo[i][1])+" y;"+String.valueOf(refinfo[i][2]));
            }
        }
        IJ.log("background mean;"+backgroundvalue);
        
        for(int i=0;i<indexes.length;i++)//rot roi processing part
        {
            if(isrot[i])
            {
                //if the axis and centroid of parent roi had measued, dont measure again
                int currentslicenum;
                currentslicenum=imp.getCurrentSlice();
                IJ.log("############################ Slice num:"+currentslicenum);
                double[] parentdata;
                Roi parentroi=(Roi) Rois.get(Roilist.getItem((int)rotinfo[i][0]));
                java.awt.Rectangle boundary;
                boundary=parentroi.getBounds();
                double parentwidth=boundary.width;
                double parentheight=boundary.height;
                //int parentlrshiftx=avelrshiftofeachrois[(int)rotinfo[i][0]][0];
                //int parentlrshifty=avelrshiftofeachrois[(int)rotinfo[i][0]][1];
                //rotinfo[i][0] has parent roi index
                if(parentrotinfo[currentslicenum][(int)rotinfo[i][0]][0]==0)//initial value must be 0.0. NaN should be better, but... needs more code.
                {
                    //rotinfo[i][0] has parent roi index
                    parentdata=detectAxis(ip, imp, parentroi);//parentdata=[xcentroid,ycentroid,maxtheta]
                    //parentrotinfo[slicenum][roiindex][xcentroid,ycentroid,maxtheta] 
                    //if the change of theta is bigger than 90degree and smaller than 270, add 180degree(assume sample doesnt rotate so fast)
                    if(Math.cos(parentrotinfo[currentslicenum-1][(int)rotinfo[i][0]][2]-parentdata[2])<0)
                    {
                        parentdata[2]=parentdata[2]+Math.PI;
                        //IJ.log("actual maxtheta: "+parentdata[2]/Math.PI*180);
                    }
                    parentrotinfo[currentslicenum][(int)rotinfo[i][0]]=parentdata;//[][][2] works fine but now seems strange?
                }
                else
                {
                    parentdata=parentrotinfo[currentslicenum][(int)rotinfo[i][0]];
                }
                IJ.log("parentinfo xcent; "+parentrotinfo[currentslicenum][(int)rotinfo[i][0]][0]+" ycent: "+parentrotinfo[currentslicenum][(int)rotinfo[i][0]][1]+" maxtheta: "+parentrotinfo[currentslicenum][(int)rotinfo[i][0]][2]);
                IJ.log("parentdata xcent: "+parentdata[0]+" ycent: "+parentdata[1]+" maxtheta; "+parentdata[2]);
                //rotinfo[i][1] is distance, rotinfo[i][2] is phi(angle between theta and child)
                double childangle=parentdata[2]-rotinfo[i][2];
                double xunit=Math.cos(childangle);
                double yunit=Math.sin(childangle);
                Roi temproi=(Roi) Rois.get(Roilist.getItem(indexes[i]));
                imp.setRoi(temproi);
                boundary=temproi.getBounds();
                //temproi.setLocation((int)(parentdata[0]+parentlrshiftx+xunit*rotinfo[i][1]-(boundary.width)/2),(int)(parentdata[1]+parentlrshifty+yunit*rotinfo[i][1]-(boundary.height)/2));
                temproi.setLocation((int)(returnval[(int)(rotinfo[i][0])*3]+parentwidth/2+xunit*rotinfo[i][1]-(boundary.width)/2),(int)(returnval[(int)(rotinfo[i][0])*3+1]+parentheight/2+yunit*rotinfo[i][1]-(boundary.height)/2));
                imp.setRoi(temproi);
                boundary=temproi.getBounds();
                imstat=imp.getStatistics(2);
                returnval[i*3]=boundary.x;
                returnval[i*3+1]=boundary.y;
                returnval[i*3+2]=imstat.mean;
                IJ.log("imstat.mean: "+imstat.mean);
            }
        }
        return returnval; //x,y,mean datas
    }
    
    
    /////////////////////////////////////////////////measrue rot
    //detect longitudinal axis by scanning sumof intensity along with the diamater line. the maximum theta is used as axis
    //return xcentroid, ycentroid, maxtheta
    public double[] detectAxis(ImageProcessor ip, ImagePlus imp, Roi roi){
        ImageStatistics imstat;
        imp.setRoi(roi);
        java.awt.Rectangle boundary=roi.getBounds();
        imstat=imp.getStatistics(32);
        double xcenter=imstat.xCentroid;
        double ycenter=imstat.yCentroid;
        int roix=boundary.x;
        int roiy=boundary.y;
        int roiwidth=boundary.width;
        int roiheight=boundary.height;
        double radius=roiwidth/2;//circular pseudoroi is assumed here
        double maxintensity=0;
        double maxtheta=0;
        double theta=0;
        double intensityarray[];
        //IJ.log(String.valueOf(Math.cos(60/180*(Math.PI))));
        //if(true) return 0;
        intensityarray=new double[180];
        for(int j=0;j<180;j++)
        {
            theta=Math.PI*j/180;
            //double circxunit=Math.cos(Math.PI*theta/180);
            //double circyunit=Math.sin(Math.PI*theta/180);
            double circxunit=Math.cos(theta);//unit is radian
            double circyunit=Math.sin(theta);
            //IJ.log("circxunit:"+String.valueOf(circxunit)+" circyunit:"+String.valueOf(circyunit));
            //IJ.log("xcentroid:"+String.valueOf(xcenter)+" ycentroid:"+String.valueOf(ycenter));
            double sumofintensity=0;
            for(int i=0;i<roiwidth;i++)
            {
                double circx=xcenter+circxunit*(radius-i);
                double circy=ycenter+circyunit*(radius-i);
                double pixvalue=ip.getInterpolatedValue(circx, circy);
                //IJ.log("circx:"+circx+" circy"+circy+" pixvalue:"+pixvalue);
                sumofintensity=sumofintensity+pixvalue;
            }
            //IJ.log("Sum:"+sumofintensity);
            //if(sumofintensity>maxintensity)
            //{
                //maxintensity=sumofintensity;
                //maxtheta=theta;
            //}
            intensityarray[j]=sumofintensity;
        }
        //IJ.log("maxintensity:"+maxintensity+" maxtheta:"+maxtheta/Math.PI*180);
        //double[] returnval= {xcenter,ycenter,maxtheta};
        double[] smarray=boxCar(intensityarray, 20, true);//smoothen the raw data to stabilize the angle
        double smmax=0;
        for(int i=0;i<180;i++)
        {
            theta=Math.PI*i/180;
            if(smarray[i]>smmax)
            {
                smmax=smarray[i];
                maxtheta=theta;
            }
        }
        IJ.log("maxintensity:"+maxintensity+" maxtheta:"+maxtheta/Math.PI*180);
        double[] returnval= {xcenter,ycenter,maxtheta};
        return returnval;
    }
    
    //This method was written for better axis detection of rot, but seems not improve?
    //boxcar smoothing method. if circ is true, use circuation array as input
    //window is Not width of window. half of window -1.
    public double[] boxCar(double[] array, int window, boolean circ)
    {
        double[] returnval=new double[array.length];
        for(int i=0;i<array.length;i++)
        {
            double sumoflocal=0;
            int denominator=window*2+1;
            for(int k=-window;k<=window;k++)
            {
                if(i+k<0)
                {
                    if(circ)
                    {
                        sumoflocal=sumoflocal+array[array.length+i+k];
                    }
                    else
                    {
                        sumoflocal=sumoflocal+0;
                        denominator=denominator-1;
                    }
                }
                else if (i+k>=array.length)
                {
                    if(circ)
                    {
                        sumoflocal=sumoflocal+array[i+k-array.length];
                    }
                    else
                    {
                        sumoflocal=sumoflocal+0;
                        denominator=denominator-1;
                    }
                }
                else
                {
                    sumoflocal=sumoflocal+array[i+k];
                }
            }
            returnval[i]=sumoflocal/denominator;
        }
        return returnval;
    }
    
    public double[] boxCar(double[] array, int window)
    {
        return boxCar(array, window, false);
    }

}

////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////
// To watch the process during data collection, use different thread.
class DataCollect extends Thread {
    DVtracer_16 tpf;
    
    DataCollect(DVtracer_16 tpf){
        this.tpf=tpf;
    }
    
    public void run()
    {
        tpf.startTrace();
    }
}

