# -------------------------------------------------------------------------
# SCRIPT NAME: GoProMax_Hero_Workflow_v4.3.0.py
# VERSION: 4.3.0
# AUTHOR: Michel Faken / Gemini
# DESCRIPTION: Comprehensive workflow tool for processing GoPro video files for Mapillary and Streetview Studio (SVS).
#              It handles Max 360 footage (11-step Max 1/2 logic, Nadir, SVS Fixes) and
#              GoPro Hero standard video footage (Hero sampling/processing/upload logic).
# -------------------------------------------------------------------------

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import os
import sys
import json
import time
import re
import math
from datetime import datetime, timezone
from pathlib import Path
import subprocess
import shutil
import threading 
import queue 
import xml.etree.ElementTree as ET
import webbrowser 

# --- Imports for Logo ---
from PIL import Image, ImageTk

# --- User Abort Control Class ---
class UserAbortException(Exception):
    """Custom exception raised when the user manually aborts the workflow."""
    pass

# --- Windows specific flag to suppress pop-up windows ---
CREATE_NO_WINDOW = 0x08000000 

# --- Resource Path Fix for PyInstaller ---
def resource_path(relative_path):
    """
    Gets the absolute path to a resource, works for both:
    1. Python script running locally
    2. PyInstaller onefile executable
    """
    # 1. Check for compiled environment
    if getattr(sys, 'frozen', False):
        # Use the base (temporary folder) where PyInstaller unpacks the files
        base_path = Path(sys._MEIPASS)
    else:
        # Use the folder where the .py file runs
        try:
            base_path = Path(__file__).resolve().parent
        except NameError:
            base_path = Path(os.getcwd()) # Fallback

    return base_path / relative_path

# --- Path Configuration (Corrected for EXE and Config) ---
SETTINGS_FILE_NAME = "mapillary_config_v4.json"

if getattr(sys, 'frozen', False):
    # Running as a PyInstaller executable: use the EXE folder
    APPLICATION_DIR = Path(sys.executable).resolve().parent
else:
    # Running as a regular Python script: use the .py file's folder
    try:
        APPLICATION_DIR = Path(__file__).resolve().parent
    except NameError:
        APPLICATION_DIR = Path(os.getcwd()) # Fallback

SETTINGS_FILE_PATH = APPLICATION_DIR / SETTINGS_FILE_NAME

# --- Global Constants ---
NADIR_SUFFIX = "_nadir"
MAPILLARY_UPLOAD_WORKERS = 8
REQUIRED_TOOLS = ["exiftool.exe", "ffmpeg.exe", "ffprobe.exe", "mapillary_tools.exe"]

# --- Global Constants for GPX fix ---
GPX_NAMESPACE_URI = "http://www.topografix.com/GPX/1/0"
GPX_TIME_TAG = f"{{{GPX_NAMESPACE_URI}}}time"
ET.register_namespace('', GPX_NAMESPACE_URI)

# --- HELPER CLASS FOR TOOLTIPS ---
class ToolTip(object):
    """Robust tooltip implementation for Tkinter."""
    def __init__(self, widget):
        self.widget = widget
        self.tipwindow = None
        self.id = None
        self.x = self.y = 0

    def showtip(self, text):
        "Display text in tooltip window"
        self.text = text
        if self.tipwindow or not self.text:
            return
        
        try:
            x = self.widget.winfo_rootx() + 20
            y = self.widget.winfo_rooty() + self.widget.winfo_height() + 5
        except:
            return

        self.tipwindow = tw = tk.Toplevel(self.widget)
        tw.wm_overrideredirect(1)
        tw.wm_geometry("+%d+%d" % (x, y))

        label = tk.Label(tw, text=self.text, justify=tk.LEFT,
                         background="#ffffe0", relief=tk.SOLID, borderwidth=1,
                         font=("tahoma", "8", "normal"))
        label.pack(ipadx=1)

    def hidetip(self):
        tw = self.tipwindow
        self.tipwindow = None
        if tw:
            tw.destroy()

def create_tooltip(widget, text):
    """Binds a tooltip to a widget with delay handling."""
    toolTip = ToolTip(widget)
    
    def enter(event):
        if toolTip.id:
            widget.after_cancel(toolTip.id)
        toolTip.id = widget.after(500, lambda: toolTip.showtip(text))
    
    def leave(event):
        if toolTip.id:
            widget.after_cancel(toolTip.id)
            toolTip.id = None
        toolTip.hidetip()
        
    widget.bind('<Enter>', enter)
    widget.bind('<Leave>', leave)
    widget.bind('<ButtonPress>', leave)

# --- TKINTER GUI CLASS ---

class MapillaryApp:
    def __init__(self, master, system_bg_color):
        self.master = master
        self.system_bg_color = system_bg_color 
        self.white_bg_color = 'white' 
        
        master.title("GoPro Max & Hero - Mapillary & SVS Workflow Tool (V4.3.0)")
        
        master.resizable(True, True) 
        master.minsize(width=850, height=1000) 

        # --- Load Logo ---
        self.logo_image = None  
        try:
            logo_path = resource_path("GoProMax_Mapillary_Streetview.png")
            if logo_path.exists():
                pil_image = Image.open(logo_path)
                pil_image.thumbnail((200, 200)) 
                self.logo_image = ImageTk.PhotoImage(pil_image)
            else:
                print(f"Logo file not found at: {logo_path}")
        except Exception as e:
            print(f"Error loading logo: {e}")
            
        # --- LOGGING SETUP ---
        if getattr(sys, 'frozen', False):
            application_path = os.path.dirname(sys.executable)
        else:
            application_path = os.path.dirname(os.path.abspath(__file__))

        # 1. Define Log Directories
        logs_base_dir = os.path.join(application_path, "logs")
        logs_std_dir = os.path.join(logs_base_dir, "standard")
        logs_ext_dir = os.path.join(logs_base_dir, "extended")

        # 2. Create directories if they don't exist
        os.makedirs(logs_std_dir, exist_ok=True)
        os.makedirs(logs_ext_dir, exist_ok=True)

        # 3. Define File Paths
        timestamp_filename = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.log_file_path = os.path.join(logs_std_dir, f"Workflow_Log_{timestamp_filename}.txt")
        self.log_file_extended_path = os.path.join(logs_ext_dir, f"Workflow_Log_{timestamp_filename}_extended.txt")
        
        try:
            # Initialize Standard Log File
            with open(self.log_file_path, "w", encoding="utf-8") as f:
                f.write(f"--- Workflow Log Started: {timestamp_filename} ---\n")
                f.write("--- Script Version: 4.2.4 ---\n\n")
            
            # Initialize Extended Log File
            with open(self.log_file_extended_path, "w", encoding="utf-8") as f:
                f.write(f"--- Extended Workflow Log Started: {timestamp_filename} ---\n")
                f.write("--- Contains full output from external tools (FFmpeg, ExifTool, Mapillary) ---\n\n")
                
        except Exception as e:
            print(f"Error creating log file: {e}")

        # ... (Start variable initialization) ...
        self.log_text = None
        self.log_text_extended = None # NEW: Variable for the extended text widget

        # --- Settings Dictionary ---
        self.settings = {
            'SourceDir': "", 'TargetDir': "", 'UtilityPath': "", 'ExifToolPath': "",
            'FFmpegPath': "", 'FFprobePath': "", 'MapillaryToolsPath': "", 'GpxFormatPath': "",
            'ImageMagickPath': "", 'NadirImagePath': "", 'NadirScaleFactor': 0.3333,
            'MapillaryUserName': "", 'VideoSampleDistance': 3.0, 'FileSuffix': "",
            'MapillaryUploadWorkers': 8, 'RunGeospatialSteps': False, 'RemoveGpsFromMp4': False,
            'RunCorePrep': False, 'RunGPX': False, 'RunSVSHeaderFix': False, 'RunSample': False,
            'RunProcess': False, 'RunUpload': False, 'RunNadirPatch': False,
            'TotalVideosProcessed': 0, 'TotalImagesProcessed': 0, 'StartTime': None,
            'CameraModel': 'Max 2' # Default value
        }

        # Tkinter variables for UI fields
        self.source_dir_var = tk.StringVar(value="")
        self.target_dir_var = tk.StringVar(value="")
        self.hero_source_dir_var = tk.StringVar(value="")
        self.hero_target_dir_var = tk.StringVar(value="")
        self.utility_path_var = tk.StringVar(value="")
        self.mapillary_user_var = tk.StringVar(value="")
        self.sample_distance_var = tk.DoubleVar(value=3.0)
        self.upload_workers_var = tk.IntVar(value=8)
        self.imagemagick_path_var = tk.StringVar(value="")
        self.nadir_image_path_var = tk.StringVar(value="")
        self.nadir_scale_var = tk.DoubleVar(value=0.3333)
        self.nadir_crf_var = tk.IntVar(value=17)
        self.run_nadir_patch_var = tk.BooleanVar(value=False)
        today_suffix = datetime.now().strftime("%d%m%Y")
        self.file_suffix_var = tk.StringVar(value=today_suffix)
        self.workflow_choice = tk.IntVar(value=1)
        self.mp4_output_var = tk.BooleanVar(value=False)
        self.gps_free_mp4_var = tk.BooleanVar(value=False)
        self.mapillary_actions_var = tk.IntVar(value=1)
        self.hero_mapillary_actions_var = tk.IntVar(value=1)
        self.use_gpu_encoding_var = tk.BooleanVar(value=False)
        self.gpu_encoder_var = tk.StringVar(value='auto')
        self.nadir_qp_var = tk.IntVar(value=24)
        self.camera_model_var = tk.StringVar(value='Max 2')
        self.dir_entries = {}
        self.log_text = None
        self.log_text_extended = None # NEW: Variable for the new text widget        
        self.tool_versions = {}
        self.stop_event = threading.Event()
        self.running_thread = None 
        self.stop_button = None
        self.progress_bar = None        
        
        # --- Main UI Structure ---
        self.notebook = ttk.Notebook(master)
        self.notebook.pack(pady=10, padx=10, expand=True, fill='both')

        # Create Tabs
        self.config_tab = ttk.Frame(self.notebook)
        self.max_tab = ttk.Frame(self.notebook)       
        self.hero_tab = ttk.Frame(self.notebook)  
        self.log_tab = ttk.Frame(self.notebook) 
        self.log_tab_extended = ttk.Frame(self.notebook) # NEW: Extended Log Tab
        self.about_tab = ttk.Frame(self.notebook) 

        self.notebook.add(self.config_tab, text='Configuration')
        self.notebook.add(self.max_tab, text='GoPro Max Workflow')
        self.notebook.add(self.hero_tab, text='GoPro Hero Workflow')
        self.notebook.add(self.log_tab, text='Output Log')
        self.notebook.add(self.log_tab_extended, text='Output Log - Extended') # NEW: Add to notebook
        self.notebook.add(self.about_tab, text='About / Help') 

        # 1. Create Log Content
        self.create_log_tab_content(self.log_tab) 
        self.create_log_extended_tab_content(self.log_tab_extended) # NEW: Build extended tab content 

        # 2. Load settings 
        settings_loaded_successfully = self.load_settings()
        
        # 3. Get and log tool versions
        self.get_tool_versions() 
        self.log_tool_versions()
        
        # 4. Force UI update
        master.update_idletasks()
        
        # 5. Create other tab content
        self.create_config_tab(self.config_tab)
        self.create_max_workflow_tab(self.max_tab)    
        self.create_hero_workflow_tab(self.hero_tab) 
        self.create_about_tab(self.about_tab) 
        
        # 6. Update Log Tab Header color 
        log_header_label = self.log_tab.grid_slaves(row=0, column=0)[0] 
        log_header_label.config(bg=self.system_bg_color)
        
        if settings_loaded_successfully:
            self.log_message("Application started. Settings loaded. Defaulting to 'GoPro Max Workflow' tab.", 'info')
        else:
            self.log_message("Application started. Settings failed to load. Please go to the 'Configuration' tab to set them.", 'info')
        
        self.notebook.select(1)
        
    def log_message(self, message, message_type='info', extended_only=False):
        """
        Logs to GUI, Console, AND Text Files.
        If extended_only is True, it ONLY logs to the Extended Log tab and file.
        """
        
        # 1. Formatting Logic
        add_newline = False
        if message.startswith("\n"):
            add_newline = True
            message = message.lstrip("\n") 

        timestamp = datetime.now().strftime("[%H:%M:%S]")
        formatted_message = f"{timestamp} {message}\n"
        
        # Determine Tag
        tag = 'info'
        if message_type == 'error' or 'error' in message.lower() or 'problem' in message.lower() or 'fatal' in message.lower():
            tag = 'error'
        elif message_type == 'success' or 'success' in message.lower() or 'complete' in message.lower():
            tag = 'success'
        elif message_type == 'warning' or 'warning' in message.lower():
            tag = 'warning'
        elif message_type == 'cmd':
            tag = 'cmd'

        # --- A. WRITE TO EXTENDED LOG (Always) ---
        if self.log_text_extended:
            if add_newline:
                self.log_text_extended.insert(tk.END, "\n")
            self.log_text_extended.insert(tk.END, formatted_message, tag)
            self.log_text_extended.see(tk.END)
            try:
                self.log_text_extended.update_idletasks()
            except: pass
            
        try:
            with open(self.log_file_extended_path, "a", encoding="utf-8") as f:
                if add_newline: f.write("\n")
                f.write(formatted_message)
        except Exception as e:
            print(f"Warning: Could not write to extended log file: {e}")

        # --- B. WRITE TO STANDARD LOG (Only if not extended_only) ---
        if not extended_only:
            if self.log_text:
                if add_newline:
                    self.log_text.insert(tk.END, "\n")
                self.log_text.insert(tk.END, formatted_message, tag)
                self.log_text.see(tk.END)
                try:
                    self.log_text.update_idletasks()
                except: pass
            else:
                if add_newline: print("")
                print(formatted_message.strip())

            try:
                with open(self.log_file_path, "a", encoding="utf-8") as f:
                    if add_newline: f.write("\n")
                    f.write(formatted_message)
            except Exception as e:
                print(f"Warning: Could not write to log file: {e}")
            
    def log_tool_versions(self):
        """Logs the utility tool versions as plain text."""
        self.log_message("\n--- Installed Utility Tool Versions ---", 'info')
        
        if self.tool_versions:
            max_len = max(len(tool) for tool in self.tool_versions.keys())
            
            for tool, version in self.tool_versions.items():
                formatted_line = f"{tool.ljust(max_len)} : {version}"
                self.log_message(formatted_line, 'info')
        else:
            self.log_message("No tools detected.", 'warning')
            
        self.log_message("--- End Tool Versions ---", 'info')
            
    # --- UI Helpers ---
    def update_workflow_options(self):
        """Updates the state of the Mapillary and Streetview option frames based on the main workflow selection."""
        choice = self.workflow_choice.get()
        enable_mapillary = (choice in [1, 3])
        mapillary_state = tk.NORMAL if enable_mapillary else tk.DISABLED
        
        # Handle the buttons directly
        if hasattr(self, 'map_btn_sample_upload') and hasattr(self, 'map_btn_sample_only'):
             self.map_btn_sample_upload.config(state=mapillary_state)
             self.map_btn_sample_only.config(state=mapillary_state)


    def get_tool_versions(self):
        """Executes external tools to retrieve their version numbers."""
        self.update_settings_dict() 
        self.tool_versions = {}
        
        tool_commands = {
            "ExifTool": (self.settings['ExifToolPath'], ["-ver"]),
            "FFmpeg": (self.settings['FFmpegPath'], ["-version"]),
            "FFprobe": (self.settings['FFprobePath'], ["-version"]),
            "Mapillary Tools": (self.settings['MapillaryToolsPath'], ["--version"]),
            "ImageMagick": (self.settings['ImageMagickPath'], ["-version"])
        }
        
        creation_flags = CREATE_NO_WINDOW if os.name == 'nt' else 0

        for tool_name, (tool_path, args) in tool_commands.items():
            if not Path(tool_path).exists():
                self.tool_versions[tool_name] = "Not Found / Not Bundled" if not getattr(sys, 'frozen', False) else "Bundled / Not Found"
                continue

            command = [tool_path] + args
            try:
                result = subprocess.run(
                    command,
                    capture_output=True,
                    creationflags=creation_flags, 
                    text=True,
                    check=False,
                    timeout=5,
                    encoding='utf-8',
                    shell=False 
                )
                
                version_string = "Error"
                
                if result.returncode == 0:
                    output = result.stdout.strip()
                    if tool_name == "ExifTool":
                        version_string = output.split('\n')[0].strip()
                    elif tool_name in ["FFmpeg", "FFprobe"]:
                        match = re.search(r"version\s+([\w\.\-\_]+)", output)
                        if match:
                            version_string = match.group(1).split('\n')[0].strip()
                        else:
                            version_string = output.split('\n')[0].strip()
                    elif tool_name == "Mapillary Tools":
                        version_string = output.split('\n')[0].strip()
                    elif tool_name == "ImageMagick":
                         version_string = output.split('\n')[0].replace("Version: ", "").strip()

                self.tool_versions[tool_name] = version_string
                
            except FileNotFoundError:
                self.tool_versions[tool_name] = "Not Found"
            except subprocess.TimeoutExpired:
                 self.tool_versions[tool_name] = "Timeout"
            except Exception as e:
                self.tool_versions[tool_name] = f"Error: {e.__class__.__name__}"

    # -- NEW METHOD FOR EXTERNAL TOOLS - Replaces the standard subprocess.run calls --
    def run_external_command(self, command_list, check_error=True):
        """
        Executes an external command and logs FULL output to the Extended Log.
        Returns the return code.
        """
        cmd_str = " ".join(command_list)
        self.log_message(f"EXECUTING: {cmd_str}", 'cmd', extended_only=True)
        
        creation_flags = CREATE_NO_WINDOW if os.name == 'nt' else 0
        
        try:
            # Use Popen to capture stdout and stderr combined
            process = subprocess.Popen(
                command_list,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, # Merge stderr into stdout
                stdin=subprocess.DEVNULL,
                creationflags=creation_flags,
                text=True,
                encoding='utf-8',
                errors='replace'
            )
            
            # Read output line by line as it is generated
            for line in process.stdout:
                clean_line = line.rstrip()
                if clean_line:
                    # Log raw tool output ONLY to extended log
                    self.log_message(f"  [TOOL] {clean_line}", 'info', extended_only=True)
            
            process.wait()
            
            if process.returncode == 0:
                self.log_message(f"FINISHED: {command_list[0]}", 'success', extended_only=True)
            elif check_error:
                self.log_message(f"FAILED: {command_list[0]} (Code {process.returncode})", 'error') # Log error to both
                
            return process.returncode
            
        except Exception as e:
            self.log_message(f"CRITICAL ERROR executing {command_list[0]}: {e}", 'error')
            return -1

    # --- Configuration Functions ---
    def load_settings(self):
        """Loads settings from the JSON file and updates UI variables."""
        if SETTINGS_FILE_PATH.exists(): 
            try:
                with open(SETTINGS_FILE_PATH, 'r') as f:
                    loaded_settings = json.load(f)
                
                self.source_dir_var.set(loaded_settings.get('SourceDir', ""))
                self.target_dir_var.set(loaded_settings.get('TargetDir', ""))
                self.hero_source_dir_var.set(loaded_settings.get('HeroSourceDir', ""))
                self.hero_target_dir_var.set(loaded_settings.get('HeroTargetDir', ""))
                if not getattr(sys, 'frozen', False):
                    self.utility_path_var.set(loaded_settings.get('UtilityPath', ""))
                
                self.imagemagick_path_var.set(loaded_settings.get('ImageMagickPath', ""))
                self.nadir_image_path_var.set(loaded_settings.get('NadirImagePath', ""))
                self.nadir_scale_var.set(loaded_settings.get('NadirScaleFactor', 0.3333))
                self.nadir_crf_var.set(loaded_settings.get('NadirCRF', 17))
                self.nadir_qp_var.set(loaded_settings.get('NadirQP', 24))

                self.mapillary_user_var.set(loaded_settings.get('MapillaryUserName', ""))
                self.sample_distance_var.set(loaded_settings.get('VideoSampleDistance', 3.0))
                self.upload_workers_var.set(loaded_settings.get('MapillaryUploadWorkers', 8))
                
                default_suffix = self.file_suffix_var.get()
                self.file_suffix_var.set(loaded_settings.get('FileSuffix', default_suffix))
                self.use_gpu_encoding_var.set(loaded_settings.get('UseGPUEncoding', False))
                self.gpu_encoder_var.set(loaded_settings.get('GPUEncoder', 'auto'))
                
                self.update_settings_dict()
                return True
            except Exception as e:
                print(f"[ERROR] Error loading settings: {e}. Manual input required.")
                return False
        return False

    def save_settings(self):
        """Saves current settings to the JSON file."""
        self.update_settings_dict()
        
        utility_path_to_save = self.utility_path_var.get()
        if utility_path_to_save.startswith("[BUNDLED:"):
            utility_path_to_save = ""
            
        settings_to_save = {
            'SourceDir': self.settings['SourceDir'],
            'TargetDir': self.settings['TargetDir'],
            'HeroSourceDir': self.settings['HeroSourceDir'],
            'HeroTargetDir': self.settings['HeroTargetDir'],
            'UtilityPath': utility_path_to_save,
            
            'ImageMagickPath': self.settings['ImageMagickPath'],
            'NadirImagePath': self.settings['NadirImagePath'],
            'NadirScaleFactor': self.settings['NadirScaleFactor'],
            'NadirCRF': self.settings['NadirCRF'],
            
            'MapillaryUserName': self.settings['MapillaryUserName'],
            'VideoSampleDistance': self.settings['VideoSampleDistance'],
            'FileSuffix': self.settings['FileSuffix'],
            'MapillaryUploadWorkers': self.settings['MapillaryUploadWorkers'],
            'UseGPUEncoding': self.settings['UseGPUEncoding'],
            'GPUEncoder': self.settings['GPUEncoder'],
            'NadirQP': self.settings['NadirQP']
        }

        try:
            with open(SETTINGS_FILE_PATH, 'w') as f: 
                json.dump(settings_to_save, f, indent=4)
            self.log_message(f"[SUCCESS] Settings successfully saved to '{SETTINGS_FILE_PATH}'.", 'success')
            
        except Exception as e:
            self.log_message(f"[ERROR] Failed to save settings: {e}", 'error')

    def update_settings_dict(self):
        """Updates the internal settings dictionary."""
        self.settings['SourceDir'] = self.source_dir_var.get()
        self.settings['TargetDir'] = self.target_dir_var.get()
        self.settings['HeroSourceDir'] = self.hero_source_dir_var.get()
        self.settings['HeroTargetDir'] = self.hero_target_dir_var.get()
        self.settings['MapillaryUserName'] = self.mapillary_user_var.get()
        try: 
            self.settings['MapillaryUploadWorkers'] = self.upload_workers_var.get()
            if self.settings['MapillaryUploadWorkers'] < 1: self.settings['MapillaryUploadWorkers'] = 1
        except: 
            self.settings['MapillaryUploadWorkers'] = 8
        
        self.settings['NadirImagePath'] = self.nadir_image_path_var.get()
        try: self.settings['NadirScaleFactor'] = self.nadir_scale_var.get()
        except: self.settings['NadirScaleFactor'] = 0.3333
        
        try: self.settings['NadirCRF'] = self.nadir_crf_var.get()
        except: self.settings['NadirCRF'] = 17
        
        try:
            self.settings['VideoSampleDistance'] = self.sample_distance_var.get()
        except:
            self.settings['VideoSampleDistance'] = 3.0
            
        suffix_input = self.file_suffix_var.get().strip()
        if not suffix_input:
            self.settings['FileSuffix'] = ""
        else:
            self.settings['FileSuffix'] = re.sub(r'^\s*_*|\s*', '', suffix_input)
            
        self.settings['CameraModel'] = self.camera_model_var.get()
        self.settings['UseGPUEncoding'] = self.use_gpu_encoding_var.get()
        self.settings['GPUEncoder'] = self.gpu_encoder_var.get()
        self.settings['NadirQP'] = self.nadir_qp_var.get()

        # --- Dynamic Tool Path Determination ---
        if getattr(sys, 'frozen', False):
            tools_dir = resource_path("tools")
            self.settings['UtilityPath'] = str(tools_dir)
            self.utility_path_var.set(f"[BUNDLED: {tools_dir.name}]")
        else:
            self.settings['UtilityPath'] = self.utility_path_var.get()
            tools_dir = Path(self.settings['UtilityPath'])

        self.settings['ExifToolPath'] = str(tools_dir / "exiftool.exe")
        self.settings['FFmpegPath'] = str(tools_dir / "ffmpeg.exe")
        self.settings['MapillaryToolsPath'] = str(tools_dir / "mapillary_tools.exe")
        self.settings['GpxFormatPath'] = str(tools_dir / "gpx.fmt")
        self.settings['FFprobePath'] = str(tools_dir / "ffprobe.exe")
        
        magick_input = self.imagemagick_path_var.get().strip()
        if magick_input and Path(magick_input).exists():
            if Path(magick_input).is_file(): self.settings['ImageMagickPath'] = magick_input
            else: self.settings['ImageMagickPath'] = str(Path(magick_input) / "magick.exe")
        else:
            self.settings['ImageMagickPath'] = str(tools_dir / "magick.exe")

    def browse_directory(self, var):
        directory = filedialog.askdirectory()
        if directory:
            var.set(directory)

    def browse_file(self, var):
        filename = filedialog.askopenfilename()
        if filename:
            var.set(filename)
            
    # --- UI Creation ---
    
    def create_config_tab(self, tab):
        tab.grid_rowconfigure(0, weight=1)
        tab.grid_columnconfigure(0, weight=1)
        
        canvas = tk.Canvas(tab)
        scrollable_frame = ttk.Frame(canvas)
        scrollable_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        scrollable_frame.grid_columnconfigure(0, weight=1)
        canvas_window = canvas.create_window((0, 0), window=scrollable_frame, anchor="nw") 
        
        def on_canvas_resize(event):
            canvas.itemconfig(canvas_window, width=event.width)
        canvas.bind('<Configure>', on_canvas_resize)
        canvas.grid(row=0, column=0, sticky='nsew')
        content_frame = scrollable_frame
        
        if self.logo_image:
            pil_image_new = Image.open(resource_path("GoProMax_Mapillary_Streetview.png"))
            pil_image_new.thumbnail((100, 100)) 
            self.logo_image_small = ImageTk.PhotoImage(pil_image_new)
            tk.Label(content_frame, image=self.logo_image_small, bg=self.system_bg_color).pack(pady=(10, 5))

        # --- GOPRO MAX CONFIG ---
        max_group_frame = ttk.LabelFrame(content_frame, text="GoPro Max Directories", padding="10")
        max_group_frame.pack(padx=20, pady=(15, 5), fill='x', expand=True)
        max_input_frame = ttk.Frame(max_group_frame)
        max_input_frame.pack(padx=10, pady=5, fill='x', expand=True)
        max_input_frame.grid_columnconfigure(0, weight=1); max_input_frame.grid_columnconfigure(1, weight=1)

        self._create_input_field_grid(max_input_frame, "Max Source Directory:", self.source_dir_var, key='SourceDir',
                                 tooltip="Folder containing .360 files AND the converted .mp4 files.", row=0, col=0, colspan=2)
        self._create_input_field_grid(max_input_frame, "Max Target Directory:", self.target_dir_var, key='TargetDir',
                                 tooltip="Output folder for Max processing.", row=1, col=0, colspan=2)

        # --- GOPRO HERO CONFIG ---
        hero_group_frame = ttk.LabelFrame(content_frame, text="GoPro Hero Directories", padding="10")
        hero_group_frame.pack(padx=20, pady=5, fill='x', expand=True)
        hero_input_frame = ttk.Frame(hero_group_frame)
        hero_input_frame.pack(padx=10, pady=5, fill='x', expand=True)
        hero_input_frame.grid_columnconfigure(0, weight=1); hero_input_frame.grid_columnconfigure(1, weight=1)

        self._create_input_field_grid(hero_input_frame, "Hero Source Dir:", self.hero_source_dir_var, key='HeroSourceDir',
                                 tooltip="Folder containing standard GoPro Hero .mp4 files.", row=0, col=0, colspan=2)
        self._create_input_field_grid(hero_input_frame, "Hero Target Dir:", self.hero_target_dir_var, key='HeroTargetDir',
                                 tooltip="Output folder for Hero frames.", row=1, col=0, colspan=2)

        # --- GENERAL SETTINGS ---
        gen_group_frame = ttk.LabelFrame(content_frame, text="General Settings & Tools", padding="10")
        gen_group_frame.pack(padx=20, pady=5, fill='x', expand=True)
        gen_frame = ttk.Frame(gen_group_frame)
        gen_frame.pack(padx=10, pady=5, fill='x', expand=True)
        gen_frame.grid_columnconfigure(0, weight=1); gen_frame.grid_columnconfigure(1, weight=1)
        
        is_path_browsable = not getattr(sys, 'frozen', False)
        self._create_input_field_grid(gen_frame, "Utility Path:", self.utility_path_var, key='UtilityPath',
                                 tooltip="Folder containing exiftool, ffmpeg, etc.",
                                 is_path=is_path_browsable, state=tk.DISABLED if not is_path_browsable else tk.NORMAL, row=0, col=0, colspan=2)

        self._create_input_field_grid(gen_frame, "Mapillary Username:", self.mapillary_user_var, is_path=False, tooltip="Required for Upload.", width=30, row=1, col=0)
        self._create_input_field_grid(gen_frame, "File Suffix (Opt):", self.file_suffix_var, is_path=False, tooltip="Optional suffix.", width=30, row=1, col=1)
        self._create_input_field_grid(gen_frame, "Sample Distance (m):", self.sample_distance_var, is_path=False, tooltip="Meters.", width=30, row=2, col=0)
        self._create_input_field_grid(gen_frame, "Upload Workers:", self.upload_workers_var, is_path=False, tooltip="Threads.", width=30, row=2, col=1)

        # --- NADIR (Max Only) ---
        nadir_group_frame = ttk.LabelFrame(content_frame, text="Nadir Settings (Max Only)", padding="10")
        nadir_group_frame.pack(padx=20, pady=5, fill='x', expand=True)
        nadir_frame = ttk.Frame(nadir_group_frame)
        nadir_frame.pack(padx=10, pady=5, fill='x', expand=True)
        nadir_frame.grid_columnconfigure(0, weight=1); nadir_frame.grid_columnconfigure(1, weight=1)
        

        self._create_input_field_grid(nadir_frame, "ImageMagick Path:", self.imagemagick_path_var, key='ImageMagickPath', is_dir_only=False, tooltip="Path to magick.exe (Required for Nadir Patch).", row=0, col=0, colspan=2)
        self._create_input_field_grid(nadir_frame, "Nadir Image (PNG):", self.nadir_image_path_var, key='NadirImagePath', is_dir_only=False, tooltip="Select a PNG.", row=1, col=0, colspan=2)
        self._create_input_field_grid(nadir_frame, "Scale Factor:", self.nadir_scale_var, is_path=False, tooltip="Scale (0.0-1.0).", width=30, row=2, col=0)
        self._create_input_field_grid(nadir_frame, "Video Quality (CRF):", self.nadir_crf_var, is_path=False, tooltip="Compression level (17=Default, Lower=Better/Larger file size).", width=30, row=2, col=1)
        
        # --- GPU / Hardware Acceleration Settings ---
        gpu_group_frame = ttk.LabelFrame(content_frame, text="GPU Acceleration (Nadir & Max Encoding)", padding="10")
        gpu_group_frame.pack(padx=20, pady=5, fill='x', expand=True)
        
        gpu_frame = ttk.Frame(gpu_group_frame)
        gpu_frame.pack(padx=10, pady=5, fill='x', expand=True)
        gpu_frame.grid_columnconfigure(0, weight=1)
        gpu_frame.grid_columnconfigure(1, weight=1)
        gpu_frame.grid_columnconfigure(2, weight=1)
        gpu_frame.grid_columnconfigure(3, weight=1)

        # 1. Enable GPU Checkbox 
        if not hasattr(self, 'use_gpu_encoding_var'):
             self.use_gpu_encoding_var = tk.BooleanVar(value=self.settings.get('UseGPUEncoding', False))

        ttk.Checkbutton(gpu_frame, text="Enable GPU Encoding", variable=self.use_gpu_encoding_var, 
                        onvalue=True, offvalue=False, command=self.update_settings_dict).grid(row=0, column=0, columnspan=4, sticky='w', pady=(0, 10))
        
        # 2. Preferred Encoder
        tk.Label(gpu_frame, text="Preferred Encoder:", anchor='w', bg=self.system_bg_color).grid(row=1, column=0, sticky='w', padx=5, pady=2)
        
        encoders = ['auto (Recommended)', 'nvenc (NVIDIA)', 'qsv (Intel Quick Sync)', 'amf (AMD)']
        if not hasattr(self, 'gpu_encoder_var'):
             self.gpu_encoder_var = tk.StringVar(value=self.settings.get('GPUEncoder', 'auto'))
        
        gpu_encoder_combo = ttk.Combobox(gpu_frame, textvariable=self.gpu_encoder_var, values=encoders, state="readonly", width=22)
        gpu_encoder_combo.grid(row=1, column=1, sticky='w', padx=5, pady=2)
        gpu_encoder_combo.bind("<<ComboboxSelected>>", lambda e: self.update_settings_dict())

        # 3. GPU Quality QP
        tk.Label(gpu_frame, text="GPU Quality (QP 0-51):", anchor='w', bg=self.system_bg_color).grid(row=1, column=2, sticky='w', padx=15, pady=2)
        
        self.nadir_qp_var = tk.IntVar(value=self.settings.get('NadirQP', 24))
        
        qp_spin = ttk.Spinbox(gpu_frame, from_=0, to=51, textvariable=self.nadir_qp_var, width=5, command=self.update_settings_dict)
        qp_spin.grid(row=1, column=3, sticky='w', padx=5, pady=2)
        
        qp_spin.bind('<Return>', lambda e: self.update_settings_dict())
        qp_spin.bind('<FocusOut>', lambda e: self.update_settings_dict())

        try:
            qp_tooltip_text = (
                "GPU Quantization Parameter (QP).\n"
                "Lower value = Better Quality (Larger Files).\n"
                "Higher value = Lower Quality (Smaller Files).\n"
                "A value of ~24 is roughly equivalent to CPU CRF 17."
            )
            
            create_tooltip(qp_spin, qp_tooltip_text)
            
        except NameError:
            print("Warning: create_tooltip function not found globally.")
        except Exception as e:
            print(f"Warning: Could not create tooltips: {e}")

        # --- BUTTONS ---
        button_frame = ttk.Frame(content_frame)
        button_frame.pack(pady=20)
        ttk.Button(button_frame, text="Save Settings", command=self.save_settings, style='TButton').pack(side='left', padx=10)
        ttk.Button(button_frame, text="Reload Settings", command=self.load_settings, style='TButton').pack(side='left', padx=10)
        ttk.Button(button_frame, text="Check Config (Info)", command=self.validate_settings_info, style='TButton').pack(side='left', padx=10)
        
    def _create_input_field_grid(self, parent, label_text, var, is_path=True, key=None, is_dir_only=True, tooltip=None, state=tk.NORMAL, width=70, row=0, col=0, colspan=1):
        LABEL_WIDTH = 30 
        
        frame = ttk.Frame(parent)
        frame.grid(row=row, column=col, columnspan=colspan, sticky='ew', padx=5, pady=5) 
        
        frame.grid_columnconfigure(1, weight=1) 
        
        # 1. CREATE BUTTON (Right)
        button = None
        if is_path:
            button_text = "Browse Dir..." if is_dir_only else "Browse File..."
            if key in ['NadirImagePath', 'ImageMagickPath']:
                 is_dir_only = False
                 button_text = "Browse File..."

            browse_command = lambda: self.browse_directory(var) if is_dir_only else self.browse_file(var)
            
            button = ttk.Button(frame, text=button_text, command=browse_command, state=state, width=14)
            button.grid(row=0, column=2, padx=5, sticky='e') 

        # 2. CREATE LABEL (Left)
        label = tk.Label(frame, text=label_text, width=LABEL_WIDTH, anchor='w', bg=self.system_bg_color) 
        label.grid(row=0, column=0, padx=5, sticky='w') 

        # 3. CREATE ENTRY FIELD (Middle)
        entry = ttk.Entry(frame, textvariable=var, width=width, state=state) 
        # Zorg ervoor dat de default style 'TEntry' wordt gebruikt voor de reset
        entry.config(style='TEntry')
        entry.grid(row=0, column=1, padx=0, sticky='ew')
        
        if key: self.dir_entries[key] = entry 
        
        if tooltip:
            create_tooltip(label, tooltip)
            create_tooltip(entry, tooltip)
            if button: create_tooltip(button, tooltip)

    def check_for_abort(self, step_name):
        """Checks the stop flag and raises an exception if set."""
        if self.stop_event.is_set():
            self.log_message(f"\n[ABORTED] Workflow manually stopped during {step_name}.", 'error')
            self.log_message("\n--- WORKFLOW ABORTED ---", 'error')
            
            # Cleanup will be handled by the outer try/except block.
            raise Exception("Workflow Aborted by User")
        return False
    
    def create_max_workflow_tab(self, tab):
        tab.grid_rowconfigure(0, weight=1)
        tab.grid_columnconfigure(0, weight=1)
        
        canvas = tk.Canvas(tab)
        canvas.grid(row=0, column=0, sticky='nsew')
        
        scrollable_frame = ttk.Frame(canvas)
        
        scrollable_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        scrollable_frame.grid_columnconfigure(0, weight=1)

        canvas_window = canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        
        def on_canvas_resize(event):
            canvas.itemconfig(canvas_window, width=event.width)
            if event.height > scrollable_frame.winfo_reqheight():
                canvas.itemconfig(canvas_window, height=event.height)
        
        canvas.bind('<Configure>', on_canvas_resize)

        content_frame = scrollable_frame
        
        if self.logo_image:
            tk.Label(content_frame, image=self.logo_image, bg=self.system_bg_color).pack(pady=(10, 5))

        tk.Label(content_frame, text="GOPRO MAX WORKFLOW", font=('Arial', 12, 'bold'), bg=self.system_bg_color).pack(pady=10)
        
        pre_workflow_frame = ttk.LabelFrame(content_frame, text="Essential Pre-Workflow Step", padding="10")
        pre_workflow_frame.pack(padx=20, pady=10, fill='x')
        
        tk.Label(pre_workflow_frame, 
                 text="Before executing any steps within this tool, you must first convert your original .360 files into .mp4 files "
                      "using the GoPro Player Batch Exporter. \n"
                      "Please use the following settings in the GoPro Player Batch Exporter:\n\n"
                      "  * Codec: HEVC\n"
                      "  * Resolution: Select the resolution corresponding to your source file settings.\n"
                      "  * Bitrate: Maximum\n"
                      "  * All other options (e.g., stabilization, horizon leveling) must be checked.\n\n"
                      "Download ImageMagick and install it (Optional, only required for Nadir Patch). Download link under About / Help.\n",
                      justify=tk.LEFT,
                      bg=self.white_bg_color).pack(anchor='w', fill='x', pady=(0, 0)) 

        # --- MAIN SELECTION GRID ---        
        selection_container = ttk.LabelFrame(content_frame, text="Workflow Configuration", padding="10")
        selection_container.pack(padx=20, pady=10, fill='x', expand=True)
        
        selection_container.columnconfigure(0, weight=1, uniform="col_group")
        selection_container.columnconfigure(1, weight=1, uniform="col_group")
        selection_container.columnconfigure(2, weight=1, uniform="col_group")
        
        # --- ROW 0: Camera Model ---
        tk.Label(selection_container, text="Camera Model Selection", font=('Arial', 10, 'bold'), bg=self.system_bg_color).grid(row=0, column=0, columnspan=3, sticky='w', pady=(0, 5))
        
        ttk.Radiobutton(selection_container, text="GoPro Max 2 (2025)", variable=self.camera_model_var, value='Max 2').grid(row=1, column=0, sticky='w', padx=5)
        ttk.Radiobutton(selection_container, text="GoPro Max 1 (2019/2025)", variable=self.camera_model_var, value='Max 1').grid(row=1, column=1, sticky='w', padx=5)
        
        # --- ROW 2: Main Workflow ---
        tk.Label(selection_container, text="Choose Main Workflow", font=('Arial', 10, 'bold'), bg=self.system_bg_color).grid(row=2, column=0, columnspan=3, sticky='w', pady=(15, 5))
        
        ttk.Radiobutton(selection_container, text="1) Mapillary processing", variable=self.workflow_choice, value=1, command=self.update_workflow_options).grid(row=3, column=0, sticky='w', padx=5)
        ttk.Radiobutton(selection_container, text="2) Streetview Studio processing", variable=self.workflow_choice, value=2, command=self.update_workflow_options).grid(row=3, column=1, sticky='w', padx=5)
        ttk.Radiobutton(selection_container, text="3) Run all", variable=self.workflow_choice, value=3, command=self.update_workflow_options).grid(row=3, column=2, sticky='w', padx=5)

        # --- ROW 4: Mapillary Actions ---
        tk.Label(selection_container, text="Mapillary Actions Options", font=('Arial', 10, 'bold'), bg=self.system_bg_color).grid(row=4, column=0, columnspan=3, sticky='w', pady=(15, 5))
        
        self.map_btn_sample_upload = ttk.Radiobutton(selection_container, text="Sample, Process and Upload", variable=self.mapillary_actions_var, value=1)
        self.map_btn_sample_upload.grid(row=5, column=0, sticky='w', padx=5)
        
        self.map_btn_sample_only = ttk.Radiobutton(selection_container, text="Sample and Process Only (No Upload)", variable=self.mapillary_actions_var, value=2)
        self.map_btn_sample_only.grid(row=5, column=1, sticky='w', padx=5)

        # --- NADIR OPTION ---
        optional_frame = ttk.LabelFrame(content_frame, text="Optional Processing", padding="10")
        optional_frame.pack(padx=20, pady=10, fill='x')
        
        nadir_container = ttk.Frame(optional_frame)
        nadir_container.pack(anchor='w', fill='x', padx=5) 

        ttk.Checkbutton(nadir_container, text="Apply Nadir Patch (Requires ImageMagick)", variable=self.run_nadir_patch_var).pack(side='left')
        
        self.update_workflow_options() 
        
        button_container = ttk.Frame(content_frame, padding="20 0 20 0") 
        button_container.pack(pady=20, fill='x') 
        
        ttk.Button(button_container, text="START MAX WORKFLOW", command=self.start_max_workflow, style='Accent.Big.TButton').pack(pady=0, fill='x')
    
    def create_hero_workflow_tab(self, tab):
        tab.grid_rowconfigure(0, weight=1)
        tab.grid_columnconfigure(0, weight=1)
        
        canvas = tk.Canvas(tab); canvas.grid(row=0, column=0, sticky='nsew')
        scrollable_frame = ttk.Frame(canvas)
        scrollable_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        scrollable_frame.grid_columnconfigure(0, weight=1)
        canvas_window = canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.bind('<Configure>', lambda e: canvas.itemconfig(canvas_window, width=e.width))
        content_frame = scrollable_frame
        
        if self.logo_image:
            tk.Label(content_frame, image=self.logo_image, bg=self.system_bg_color).pack(pady=(10, 5))
        
        tk.Label(content_frame, text="GOPRO HERO WORKFLOW", font=('Arial', 12, 'bold'), bg=self.system_bg_color).pack(pady=10)
        
        info_frame = ttk.LabelFrame(content_frame, text="Workflow Info", padding="10")
        info_frame.pack(padx=20, pady=10, fill='x')
        tk.Label(info_frame, text="Processes standard .mp4 files. No ImageMagick/Nadir required.\nAfter successful upload, images are moved to 'Upload_Successful' folder.", bg='white', justify='left').pack(anchor='w', fill='x')

        selection_container = ttk.LabelFrame(content_frame, text="Mapillary Actions Options", padding="10")
        selection_container.pack(padx=20, pady=10, fill='x')
        
        ttk.Radiobutton(selection_container, text="Sample, Process and Upload", variable=self.hero_mapillary_actions_var, value=1).pack(anchor='w', pady=5)
        ttk.Radiobutton(selection_container, text="Sample and Process Only (No Upload)", variable=self.hero_mapillary_actions_var, value=2).pack(anchor='w', pady=5)
        
        button_container = ttk.Frame(content_frame, padding="20 0 20 0") 
        button_container.pack(pady=20, fill='x') 
        ttk.Button(button_container, text="START HERO WORKFLOW", command=self.start_hero_workflow, style='Accent.Big.TButton').pack(pady=0, fill='x')
    
    # --- LOG TABS ---
    def create_log_tab_content(self, tab):
        """Creates the log text widget, scrollbar, and controls inside the main log tab."""
        tab.grid_rowconfigure(1, weight=1) 
        tab.grid_columnconfigure(0, weight=1)
        
        # 1. Title
        tk.Label(tab, text="WORKFLOW - OUTPUT AND LOGS", font=('Arial', 12, 'bold')).grid(row=0, column=0, pady=10, sticky='n')

        # 2. Log Frame (Container for Text + Scrollbar)
        log_frame = ttk.Frame(tab)
        log_frame.grid(row=1, column=0, padx=10, pady=5, sticky='nsew')
        log_frame.grid_rowconfigure(0, weight=1)
        log_frame.grid_columnconfigure(0, weight=1)
        
        # Scrollbar
        scrollbar = ttk.Scrollbar(log_frame)
        scrollbar.grid(row=0, column=1, sticky='ns')
        
        # Text Area
        self.log_text = tk.Text(log_frame, wrap=tk.WORD, yscrollcommand=scrollbar.set, height=30, bg='white', font=('Consolas', 9))
        self.log_text.grid(row=0, column=0, sticky='nsew')
        
        scrollbar.config(command=self.log_text.yview)

        # Tags
        self.log_text.tag_config('error', foreground='red')
        self.log_text.tag_config('success', foreground='green')
        self.log_text.tag_config('warning', foreground='#FF8C00') # Orange-ish
        
        # 3. Progress & Stop Button Frame
        button_frame = ttk.Frame(tab, padding="5 0 5 0") 
        button_frame.grid(row=2, column=0, sticky='ew', padx=10, pady=(0, 10))
        
        self.progress_bar = ttk.Progressbar(button_frame, orient="horizontal", mode="determinate")
        self.progress_bar.pack(fill='x', padx=0, pady=(0, 5))

        self.stop_button = ttk.Button(
            button_frame, 
            text="STOP WORKFLOW (ABORT)", 
            command=self.stop_workflow,
            style='Stop.TButton', 
            state=tk.DISABLED 
        )
        self.stop_button.pack(fill='x', padx=0, pady=0)
        
    def create_log_extended_tab_content(self, tab):
        """Creates the text widget for the Extended Output Log (View Only)."""
        tab.grid_rowconfigure(1, weight=1) 
        tab.grid_columnconfigure(0, weight=1)

        # 1. Title (Fixed background color)
        tk.Label(
            tab, 
            text="WORKFLOW - EXTENDED OUTPUT AND LOGS", 
            font=('Arial', 12, 'bold'),
            bg=self.system_bg_color 
        ).grid(row=0, column=0, pady=10, sticky='n')
        
        # 2. Log Frame (Container)
        log_frame = ttk.Frame(tab)
        log_frame.grid(row=1, column=0, padx=10, pady=5, sticky='nsew')
        
        log_frame.grid_rowconfigure(0, weight=1)
        log_frame.grid_columnconfigure(0, weight=1)

        # 3. Text Area & Scrollbars
        self.log_text_extended = tk.Text(log_frame, state='normal', wrap='none', bg='white', font=("Consolas", 9))
        self.log_text_extended.grid(row=0, column=0, sticky='nsew')
        
        # Scrollbars
        yscroll = ttk.Scrollbar(log_frame, orient='vertical', command=self.log_text_extended.yview)
        yscroll.grid(row=0, column=1, sticky='ns')
        
        xscroll = ttk.Scrollbar(log_frame, orient='horizontal', command=self.log_text_extended.xview)
        xscroll.grid(row=1, column=0, sticky='ew')
        
        self.log_text_extended.configure(yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
        
        # Tags
        self.log_text_extended.tag_config('info', foreground='black')
        self.log_text_extended.tag_config('error', foreground='red')
        self.log_text_extended.tag_config('success', foreground='green')
        self.log_text_extended.tag_config('warning', foreground='#FF8C00')
        self.log_text_extended.tag_config('cmd', foreground='blue')
        
    # --- ABOUT TAB ---
    def create_about_tab(self, tab):
        """Creates the About / Help tab content with a modern Card-based layout (V4.0.0)."""
        tab.grid_rowconfigure(0, weight=1)
        tab.grid_columnconfigure(0, weight=1)
        
        canvas = tk.Canvas(tab, bg=self.system_bg_color)
        canvas.grid(row=0, column=0, sticky='nsew')
        
        scrollable_frame = ttk.Frame(canvas)
        scrollable_frame.grid_columnconfigure(0, weight=1)

        style = ttk.Style(self.master)
        style.configure('Base.TFrame', background=self.system_bg_color)
        
        scrollable_frame.config(style='Base.TFrame')

        canvas_window = canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        
        def on_canvas_resize(event):
            canvas.itemconfig(canvas_window, width=event.width)
            canvas.config(scrollregion=canvas.bbox("all"))

        scrollable_frame.bind("<Configure>", on_canvas_resize)
        canvas.bind('<Configure>', on_canvas_resize) 
        
        content = scrollable_frame
        
        # --- Helper for Cards ---
        def create_card(parent, title):
            outer_frame = ttk.Frame(parent, padding=(20, 10, 20, 5), style='Base.TFrame')
            outer_frame.pack(fill='x', expand=True)
            
            card = tk.Frame(outer_frame, bg='white', highlightbackground='#d0d0d0', highlightthickness=1)
            card.pack(fill='x', expand=True)
            
            if title:
                tk.Label(card, text=title, font=('Arial', 12, 'bold'), fg='#EC9C4E', bg='white').pack(anchor='w', padx=15, pady=(15, 10))
                ttk.Separator(card, orient='horizontal').pack(fill='x', padx=15, pady=(0, 10))
            
            container = tk.Frame(card, bg='white', padx=15, pady=0)
            container.pack(fill='x', expand=True, pady=(0, 15)) 
            
            return container

        # --- HEADER ---
        header_frame = tk.Frame(content, bg=self.system_bg_color, pady=20)
        header_frame.pack(fill='x')
        tk.Label(header_frame, text="GoPro Max & Hero Workflow Tool", font=('Arial', 20, 'bold'), bg=self.system_bg_color).pack()
        tk.Label(header_frame, text="Version 4.3.0 (Max 1 & 2 + Hero Edition)", font=('Arial', 10, 'bold'), fg='#666', bg=self.system_bg_color).pack()
        tk.Label(header_frame, text="Author: Michel / thewizard (Mapillary username)", font=('Arial', 9), fg='#666', bg=self.system_bg_color).pack()

        # --- CARD 1: MAX WORKFLOW ---
        card_max = create_card(content, "GoPro Max Workflow")
        msg_max = (
            "This workflow processes 360-degree video files (.360 & converted .mp4) for Mapillary and/or Streetview Studio (SVS). "
            "It handles GPMF extraction, video/metadata muxing, and prepares final output packages."
        )
        tk.Label(card_max, text=msg_max, bg='white', justify='left', anchor='w', wraplength=750).pack(fill='x', pady=(0, 10))
        
        grid_wf = tk.Frame(card_max, bg='white')
        grid_wf.pack(fill='x')
        grid_wf.grid_columnconfigure(0, weight=1)
        grid_wf.grid_columnconfigure(1, weight=1)
        
        tk.Label(grid_wf, text="Max 2 Logic:", font=('Arial', 10, 'bold'), bg='white', fg='#47A9A3').grid(row=0, column=0, sticky='w')
        msg_max2 = "• Creates SVS-ready package (MP4 + GPX + Header Fix)\n• Full Mapillary preparation"
        tk.Label(grid_wf, text=msg_max2, bg='white', justify='left', anchor='w').grid(row=1, column=0, sticky='nw', pady=(5,0))

        tk.Label(grid_wf, text="Max 1 Logic:", font=('Arial', 10, 'bold'), bg='white', fg='#47A9A3').grid(row=0, column=1, sticky='w')
        msg_max1 = "• Creates clean MP4 for SVS (no GPX/header fix required)\n• Full Mapillary preparation"
        tk.Label(grid_wf, text=msg_max1, bg='white', justify='left', anchor='w').grid(row=1, column=1, sticky='nw', pady=(5,0))

        # --- CARD 2: HERO WORKFLOW (NEW) ---
        card_hero = create_card(content, "GoPro Hero Workflow")
        msg_hero = (
            "This dedicated workflow processes standard GoPro Hero MP4 files directly for Mapillary. "
            "It extracts GPS data during frame sampling, processes the frames, and optionally uploads them. No Nadir/SVS logic applies."
        )
        tk.Label(card_hero, text=msg_hero, bg='white', justify='left', anchor='w', wraplength=750).pack(fill='x', pady=(0, 10))

        # --- CARD 3: PRE-WORKFLOW & NADIR ---
        card_prep = create_card(content, "Optional Nadir")
        msg_prep = (
            "Nadir Patch (Optional, Max Only): If selected, you MUST provide a path to a PNG image and have ImageMagick (magick.exe) installed."
        )
        tk.Label(card_prep, text=msg_prep, bg='white', justify='left', anchor='w', wraplength=750).pack(fill='x', pady=(0, 10))

        # --- CARD 4: EXTERNAL TOOLS ---
        card_tools = create_card(content, "External Utilities")
        
        tk.Label(card_tools, 
                 text="Most tools (ExifTool, FFmpeg, Mapillary Tools) are bundled. ImageMagick is required only for the Nadir Patch feature.", 
                 bg='white', wraplength=750, justify='left').pack(anchor='w', pady=(0,10))
        
        tools_grid = tk.Frame(card_tools, bg='white')
        tools_grid.pack(fill='x')
        
        def add_tool_link(name, desc, url, row):
            tk.Label(tools_grid, text=f"• {name}:", font=('Arial', 9, 'bold'), bg='white').grid(row=row, column=0, sticky='w', pady=2)
            tk.Label(tools_grid, text=desc, bg='white').grid(row=row, column=1, sticky='w', padx=10)
            
            if url:
                link = tk.Label(tools_grid, text="[Download]", fg='#47A9A3', cursor='hand2', bg='white', font=('Arial', 9, 'underline'))
                link.grid(row=row, column=2, sticky='e')
                link.bind("<Button-1>", lambda e: webbrowser.open_new(url))
        
        add_tool_link("ImageMagick", "Required for Nadir Patch (magick.exe)", "https://imagemagick.org/script/download.php#windows", 0)
        add_tool_link("ExifTool", "Extracts metadata, generates GPX, synchronizes time.", "https://exiftool.org/", 1)
        add_tool_link("FFmpeg/FFprobe", "Video processing, muxing, GPS extraction.", "https://ffmpeg.org/", 2)
        add_tool_link("Mapillary Tools", "Samples video frames and handles uploads.", "https://github.com/mapillary/mapillary_tools", 3)


        # --- CARD 5: DISCLAIMER ---
        card_disc = create_card(content, None) 
        tk.Label(card_disc, text="LIMITATION OF LIABILITY & WARRANTY", font=('Arial', 8, 'bold'), fg='#999', bg='white').pack(anchor='w')
        
        disclaimer_text = (
            "This software is provided 'AS IS', without warranty of any kind, express or implied, including but not limited to the warranties of merchantability, "
            "fitness for a particular purpose and non-infringement. In no event shall the author (Michel / thewizard) be liable for any claim, damages or other liability, "
            "whether in an action of contract, tort or otherwise, arising from, out of or in connection with the software or the use or other dealings in the software.\n\n"
            "THIRD PARTY TOOLS: This workflow relies on external third-party executables (FFmpeg, ExifTool, Mapillary Tools, ImageMagick). By using this software, you acknowledge "
            "and agree to comply with the respective licenses and terms of use of these third-party tools. The author of this workflow tool assumes no responsibility "
            "for the functionality, updates, or licensing changes of these external dependencies."
        )
        
        tk.Label(card_disc, 
                 text=disclaimer_text, 
                 font=('Arial', 7), fg='#999', bg='white', wraplength=750, justify='left').pack(anchor='w', pady=(5,0))

        tk.Label(content, text="", bg=self.system_bg_color).pack(pady=10)
    
    # --- Validation and Execution ---
    def _set_entry_color(self, key, is_valid):
        """Sets the fieldbackground color of a configuration entry widget using ttk styles."""
        if key in self.dir_entries:
            style_name = 'Valid.TEntry' if is_valid else 'Invalid.TEntry'
            
            style = ttk.Style(self.master)
            
            style.configure('Valid.TEntry', fieldbackground='lightgreen')
            style.configure('Invalid.TEntry', fieldbackground='pink')
            
            self.dir_entries[key].config(style=style_name)
    
    def validate_settings_info(self):
        """Soft validation for Config Button."""
        self.update_settings_dict()
        msg = []
        if self.settings['SourceDir'] and Path(self.settings['SourceDir']).is_dir(): msg.append("Max Source: OK")
        else: msg.append("Max Source: Missing")
        if self.settings['HeroSourceDir'] and Path(self.settings['HeroSourceDir']).is_dir(): msg.append("Hero Source: OK")
        else: msg.append("Hero Source: Missing")
        messagebox.showinfo("Config Status", "\n".join(msg))

    def validate_runtime(self, mode):
        """Hard validation before run."""
        self.update_settings_dict()
        self.log_text.delete('1.0', tk.END)
        self.log_message(f"--- VALIDATING FOR {mode.upper()} ---", 'info')
        valid = True
        
        if self.tool_versions.get("Mapillary Tools") in ["Not Found", "Error"]:
            self.log_message("[FATAL] Mapillary Tools missing.", 'error'); valid = False

        if mode == 'max':
            if not Path(self.settings['SourceDir']).is_dir(): self.log_message("[FATAL] Max Source invalid.", 'error'); valid = False
            if not Path(self.settings['TargetDir']).is_dir(): self.log_message("[FATAL] Max Target invalid.", 'error'); valid = False
        elif mode == 'hero':
            if not Path(self.settings['HeroSourceDir']).is_dir(): self.log_message("[FATAL] Hero Source invalid.", 'error'); valid = False
            if not Path(self.settings['HeroTargetDir']).is_dir(): self.log_message("[FATAL] Hero Target invalid.", 'error'); valid = False
            
        if valid: self.log_message("Validation OK.", 'success')
        return valid

    def start_max_workflow(self):
        if not self.validate_runtime('max'): return
        self.update_flags_from_ui()
        
        if self.running_thread and self.running_thread.is_alive():
             self.log_message("[FATAL] Another workflow is already running. Please stop it first.", 'error')
             messagebox.showerror("Runtime Error", "Another workflow is currently active.")
             return
             
        self.notebook.select(self.log_tab)
        
        # --- THREAD CONTROL INIT ---
        self.stop_event.clear()
        if self.stop_button: self.stop_button.config(state=tk.NORMAL)
        
        workflow_thread = threading.Thread(target=self.run_workflow)
        self.running_thread = workflow_thread
        workflow_thread.start()

    def start_hero_workflow(self):
        if not self.validate_runtime('hero'): return
        
        if self.running_thread and self.running_thread.is_alive():
             self.log_message("[FATAL] Another workflow is already running. Please stop it first.", 'error')
             messagebox.showerror("Runtime Error", "Another workflow is currently active.")
             return

        act = self.hero_mapillary_actions_var.get()
        self.settings['RunSample'] = True
        self.settings['RunProcess'] = True
        self.settings['RunUpload'] = (act == 1)
        self.notebook.select(self.log_tab)
        
        # --- THREAD CONTROL INIT ---
        self.stop_event.clear()
        if self.stop_button: self.stop_button.config(state=tk.NORMAL)

        workflow_thread = threading.Thread(target=self.run_hero_workflow_logic)
        self.running_thread = workflow_thread
        workflow_thread.start()
        
    def _cleanup_after_workflow(self):
        """Common cleanup steps after workflow completes or is aborted."""
        if self.stop_button:
            self.stop_button.config(state=tk.DISABLED)
        self.running_thread = None 
        self.stop_event.clear() 

    def stop_workflow(self):
        """Signals the running thread to stop gracefully."""
        if self.running_thread and self.running_thread.is_alive():
            self.stop_event.set() 
            self.log_message("\n[WARNING] STOP signal received. Aborting workflow at next safe point...", 'error')
            
            if self.stop_button:
                 self.stop_button.config(state=tk.DISABLED)
        else:
            self.log_message("[INFO] No active workflow thread found.", 'info')
            
    def update_progress(self, current_step, total_steps):
        """Updates the progress bar and UI."""
        if hasattr(self, 'progress_bar') and self.progress_bar is not None and total_steps > 0:
            percentage = (current_step / total_steps) * 100
            self.progress_bar['value'] = percentage

            self.master.update_idletasks() 
            return percentage
        return 0
            
    def check_for_abort(self, step_name):
        """Checks the stop flag and raises an exception if set."""
        if self.stop_event.is_set():
            raise UserAbortException(f"Workflow manually stopped during {step_name}.")
        return False
            
    def _get_first_gpx_time_for_fixer(self, gpx_path: Path):
        if not gpx_path.is_file():
            self.log_message(f"    [ERROR] SVS Fix: GPX file not found at: {gpx_path}", 'error')
            return None, None
            
        try:
            tree = ET.parse(gpx_path)
            root = tree.getroot()
            
            time_element = root.find(f'.//{{{GPX_NAMESPACE_URI}}}trkpt/{{{GPX_NAMESPACE_URI}}}time')
            if time_element is None:
                time_element = root.find(f'.//{{{GPX_NAMESPACE_URI}}}time')

            if time_element is None:
                self.log_message(f"    [ERROR] SVS Fix: No valid <time> tag found in {gpx_path.name}.", 'error')
                return None, None

            gpx_time_str = time_element.text.strip()
            
            # The time string often looks like '2025-12-08T10:43:58.000Z'
            # We need to strip the milliseconds and 'Z' for Python's datetime parser
            dt_obj = datetime.strptime(gpx_time_str.split('.')[0].rstrip('Z'), "%Y-%m-%dT%H:%M:%S")

            exiftool_time_format = dt_obj.strftime("%Y:%m:%d %H:%M:%S")

            self.log_message(f"    [INFO] SVS Fix: Found GPX Start Time: {gpx_time_str}", 'info')
            return gpx_time_str, exiftool_time_format
        except Exception as e:
            self.log_message(f"    [ERROR] SVS Fix: Error reading GPX start time for {gpx_path.name}: {e}", 'error')
            return None, None
            
    def _generate_verification_log(self, gpx_utc_time, verification_output, expected_exiftool_time):
        """Verifies the ExifTool output for the SVS fix. Checks if at least 6 date fields were written successfully, ignoring consolidated tag names in the output."""
        log = [
            "*** SVS Header Verification Log ***",
            f"GPX Start Time (UTC): {gpx_utc_time}",
            f"Expected MP4 Header Time: {expected_exiftool_time}",
            "+----------------------------+-------------------------+-------------------------+"
        ]
        
        # We expect 6 successful date entries to be set to the exact time.
        # ExifTool often consolidates the names (e.g., all 3 "CreateDate" variations are outputted as "Create Date").
        success_count = 0
        
        for line in verification_output.splitlines():
            match = re.search(r"(\w+ [A-Z|a-z| ]+)\s+:\s+(.*)", line)
            
            if match:
                field_name = match.group(1).strip()
                field_value = match.group(2).strip()
                
                if 'Date' in field_name:
                    if expected_exiftool_time in field_value:
                        status = "CORRECT"
                        success_count += 1
                    else:
                        status = "ERROR - TIME MISMATCH"
                        
                    log.append(f"| {field_name:<26} | {field_value:<23} | {status:<23} |")

        log.append("+----------------------------+-------------------------+-------------------------+")

        # SVS requires 6 distinct date fields to be synchronized.
        all_correct = (success_count >= 6)
        
        if success_count < 6:
             final_status = f"INCOMPLETE (Found {success_count}/6 synchronized dates!)"
             log.append(f"Verification Result: Only {success_count} critical MP4 date fields synchronized.")
             log.append("WARNING: The structure of the generated MP4 file may not contain all 6 date atoms. SVS upload may still fail.")
        else:
             final_status = "successfully synchronized."
             log.append(f"Verification Result: All 6 critical MP4 date fields are {final_status}")

        return "\n".join(log)
    
    def _get_video_bit_depth(self, path):
    
        """Detects video stream bit depth (8 or 10) using FFprobe."""
        cmd = [
            self.settings['FFprobePath'], 
            "-v", "error", 
            "-select_streams", "v:0", 
            "-show_entries", "stream=bits_per_raw_sample:stream=pix_fmt", 
            "-of", "csv=p=0:nk=1", # Output: [bits_per_raw_sample],[pix_fmt]
            str(path)
        ]
        c, o = self.run_command(cmd)
        
        default_depth = 8
        
        if c == 0 and o.strip():

            parts = [p.strip() for p in o.strip().split(',') if p.strip()] 
            
            for part in parts:
                if part.isdigit() and int(part) >= 8:
                    return int(part)
                
                if "10" in part:
                     self.log_message(f"    [INFO] Determined 10-bit depth via pixel format check ({part}).", 'info')
                     return 10
        
        self.log_message(f"    [INFO] Bit-depth tag not detected (Normal for GoPro Max 1). Defaulting to 8-bit.", 'info')
        return default_depth
    
    def _get_video_dims(self, path):
        cmd = [self.settings['FFprobePath'], "-v", "error", "-select_streams", "v:0", "-show_entries", "stream=width,height", "-of", "csv=p=0:s=x", str(path)]
        c, o = self.run_command(cmd)
        if c == 0:
            m = re.search(r"(\d+)x(\d+)", o)
            if m: return int(m.group(1)), int(m.group(2))
        return None, None

    def update_flags_from_ui(self):
        """Maps UI selections to internal workflow flags."""
        choice = self.workflow_choice.get()
        mapillary_action = self.mapillary_actions_var.get()
        
        is_max_2 = (self.camera_model_var.get() == 'Max 2') # Nieuwe variabele
        
        self.settings['RunCorePrep'] = (choice in [1, 2, 3])
        self.settings['RunGPX'] = (choice in [2, 3])
        self.settings['RunSVSHeaderFix'] = (choice in [2, 3]) and is_max_2 
        self.settings['RunGeospatialSteps'] = False
        self.settings['RemoveGpsFromMp4'] = False
        
        if choice in [1, 3]:
            self.settings['RunSample'] = (mapillary_action in [1, 2])
            self.settings['RunProcess'] = (mapillary_action in [1, 2])
            self.settings['RunUpload'] = (mapillary_action == 1) 
        else: 
            self.settings['RunSample'] = False
            self.settings['RunProcess'] = False
            self.settings['RunUpload'] = False
            
        self.settings['RunNadirPatch'] = self.run_nadir_patch_var.get()
        self.settings['CameraModel'] = self.camera_model_var.get()


    def run_command(self, command, cwd=None, error_message="Error executing command"):
        """
        Executes an external command, logs FULL output to Extended Log, 
        and returns (returncode, stdout) for internal processing.
        """
        # Create string representation for the log
        cmd_str = " ".join([str(x) for x in command])
        tool_name = command[0].split(os.sep)[-1]  # Extract only the exe name (e.g. ffmpeg.exe)
        
        # 1. Log the START of the command to Extended Log ONLY
        self.log_message(f"EXECUTING: {cmd_str}", 'cmd', extended_only=True)
        
        creation_flags = CREATE_NO_WINDOW if os.name == 'nt' else 0
        collected_output = []
        
        try:
            # Use Popen instead of run to capture streaming output
            process = subprocess.Popen(
                command,
                cwd=cwd,
                stdout=subprocess.PIPE,     # Capture standard output
                stderr=subprocess.STDOUT,   # Redirect stderr to stdout (capture errors in same stream)
                stdin=subprocess.DEVNULL,
                creationflags=creation_flags,
                text=True,
                encoding='utf-8',
                errors='replace',           # Prevent crashes on decoding weird characters
                shell=False
            )
            
            # 2. Read output line by line as it happens
            for line in process.stdout:
                clean_line = line.rstrip()
                if clean_line:
                    # Log raw tool output ONLY to extended log
                    self.log_message(f"  [{tool_name}] {clean_line}", 'info', extended_only=True)
                    # Collect line for the return value (so the script logic can still use it)
                    collected_output.append(clean_line)
            
            process.wait()
            return_code = process.returncode
            full_output = "\n".join(collected_output)
            
            # 3. Log result
            if return_code == 0:
                self.log_message(f"FINISHED: {tool_name}", 'success', extended_only=True)
            else:
                self.log_message(f"FAILED: {tool_name} (Code {return_code})", 'error', extended_only=True)
                # If it failed, also show a small error in the MAIN log so the user knows something went wrong
                self.log_message(f"    [COMMAND FAILED] {tool_name} (Code {return_code})", 'error')
            
            return return_code, full_output

        except FileNotFoundError:
            self.log_message(f"    [FATAL ERROR] Command not found: {command[0]}", 'error')
            return 1, f"Command not found: {command[0]}"
        except Exception as e:
            self.log_message(f"    [FATAL ERROR] {error_message}: {e}", 'error')
            return 1, str(e)

    def run_workflow(self):
        """The core execution logic (Max Workflow) - STRICTLY SEPARATED CHANNELS."""
        try:
            start_time = datetime.now()
            self.settings['StartTime'] = start_time
            self.settings['TotalVideosProcessed'] = 0
            self.settings['TotalImagesProcessed'] = 0
            
            cam_model = self.settings.get('CameraModel', 'Unknown')
                
            self.log_message("[INFO] Workflow started with the following settings:", 'info')
            self.log_message(f"  Camera Model: {cam_model}", 'info')
            self.log_message(f"  Core Prep RUN: {self.settings['RunCorePrep']}", 'info')
            self.log_message(f"  GPX Generation RUN: {self.settings['RunGPX']}", 'info')
            self.log_message(f"  SVS Output RUN: {self.settings['RunSVSHeaderFix']}", 'info')
            self.log_message(f"  Mapillary Workflow RUN: {self.settings['RunSample']}", 'info')
            self.log_message(f"  Nadir Patch RUN: {self.settings['RunNadirPatch']}", 'info')

            custom_suffix = f"_{self.settings['FileSuffix']}" if self.settings['FileSuffix'] else ""
            temp_mapillary_dir = Path(self.settings['TargetDir']) / "mapillary_sampled_video_frames"
            
            nadir_work = Path(self.settings['TargetDir']) / "nadir_work"
            if self.settings['RunNadirPatch']: nadir_work.mkdir(exist_ok=True)
            
            step_counter = 0
            
            # ==============================================================================
            # PHASE 1: JOINT PREPARATION (The "Batch Script" Method)
            # ==============================================================================
            if self.settings['RunCorePrep']:
                
                # --- 1. EXTRACT GPMF METADATA ---
                step_counter += 1
                self.check_for_abort("GPMF Extraction")
                self.log_message(f"\n[STEP {step_counter}/10] Extracting GPMF metadata...", 'info')
                
                original_files = list(Path(self.settings['SourceDir']).glob("*.360"))
                total_files = len(original_files)
                self.settings['TotalVideosProcessed'] = total_files
                self.update_progress(0, total_files)

                if total_files == 0:
                    self.log_message(f"    [ERROR] No .360 files found. Core Prep aborted.", 'error')
                    self.settings['RunCorePrep'] = False 
                    
                if self.settings['RunCorePrep']:
                    for i, file in enumerate(original_files, 1):
                        self.check_for_abort("GPMF Extraction loop")
                        self.update_progress(i, total_files)
                        
                        self.log_message(f"    -> Processing file {i}/{total_files}: {file.name}", 'info')
                        gpmf_output_path = Path(self.settings['SourceDir']) / f"{file.stem}_gpmf.mov"
                        
                        command = [self.settings['FFmpegPath'], "-i", str(file), "-map", "0:3", "-c", "copy", str(gpmf_output_path), "-y"]
                        if self.run_command(command, error_message=f"FFmpeg GPMF extraction failed for {file.name}")[0] == 0:
                            self.log_message(f"    [SUCCESS] GPMF track extracted.", 'success')
                    
                # --- 2. MUX VIDEO & METADATA ---
                step_counter += 1
                self.check_for_abort("Muxing Video")
                self.log_message(f"\n[STEP {step_counter}/10] Muxing video (.mp4) and GPMF (.mov)...", 'info')
                
                video_source_files = list(Path(self.settings['SourceDir']).glob("*.mp4"))
                total_files = len(video_source_files)
                self.update_progress(0, total_files)
                
                if self.settings['RunCorePrep']:
                    for i, file in enumerate(video_source_files, 1):
                        self.check_for_abort("Muxing Video loop")
                        self.update_progress(i, total_files)
                        
                        self.log_message(f"    -> Processing file {i}/{total_files}: {file.name}", 'info')
                        gpmf_source_path = Path(self.settings['SourceDir']) / f"{file.stem}_gpmf.mov"
                        
                        intermediate_base_name = f"{file.stem}{custom_suffix}"
                        intermediate_file_name = f"{intermediate_base_name}_gpmf_final.mov"
                        final_output_path = Path(self.settings['TargetDir']) / intermediate_file_name
                        
                        input_video_mux = file
                        is_nadir = False
                        
                        if self.settings['RunNadirPatch']:
                            self.log_message("       [NADIR] Calculating patch...", 'info')
                            w, h = self._get_video_dims(file)
                            
                            if w and h:
                                # 1. Detect Bit Depth
                                bit_depth = self._get_video_bit_depth(file)
                                
                                # 2. Nadir Patch sizes
                                nadir_h = int(math.trunc(h * self.settings['NadirScaleFactor']))
                                if nadir_h % 2 != 0: nadir_h += 1
                                y_pos = h - nadir_h
                                
                                # 3. Pathnames
                                t1 = nadir_work / "t1.png"; t2 = nadir_work / "t2.png"
                                t3 = nadir_work / "t3.png"; p_img = nadir_work / "patch.png"
                                nadir_vid = nadir_work / f"{file.stem}_nadir_temp.mp4"
                                
                                mgk = self.settings['ImageMagickPath']
                                img = self.settings['NadirImagePath']
                                
                                # 4. Nadir Patch Magick Commands
                                cmds = [
                                    [mgk, img, "-rotate", "180", "-strip", str(t1)],
                                    [mgk, str(t1), "-distort", "DePolar", "0", str(t2)],
                                    [mgk, str(t2), "-flip", str(t3)],
                                    [mgk, str(t3), "-flop", str(p_img)]
                                ]
                                
                                success = True
                                for c in cmds:
                                    if self.run_command(c)[0] != 0: success = False; break
                                
                                # 5. FFmpeg Overlay Command
                                if success:
                                    pix_fmt = "yuv420p" if bit_depth == 8 else "yuv420p10le"
                                    
                                    vf = f"[1:v]scale={w}:{nadir_h}[scaled_patch];[0:v][scaled_patch]overlay=0:{y_pos},format={pix_fmt}[final_out]"
                                    
                                    # === GPU ENCODER LOGICA START ===
                                    if self.settings['UseGPUEncoding']:
                                        self.log_message(f"       [NADIR] Attempting GPU encoding ({self.settings['GPUEncoder']})...", 'info')
                                        
                                        encoder_choice = self.settings['GPUEncoder'].split(' ')[0]
                                        encoder_name = ""
                                        hwaccel_args = []
                                        
                                        if encoder_choice in ['nvenc', 'auto']:
                                            # NVIDIA NVENC
                                            encoder_name = "hevc_nvenc"
                                            
                                        elif encoder_choice == 'qsv':
                                            encoder_name = "hevc_qsv"
                                            hwaccel_args = ["-hwaccel", "qsv"]
                                            
                                        elif encoder_choice == 'amf':
                                            # AMD AMF
                                            encoder_name = "hevc_amf"
                                        
                                        qp_val = self.settings.get('NadirQP', 24)
        
                                        encoder_args = [
                                           "-c:v", encoder_name, 
                                           "-qp", str(qp_val), 
                                           "-tag:v", "hvc1", 
                                           "-c:a", "copy"
                                        ]

                                        c_ov = [self.settings['FFmpegPath'], "-y"] + hwaccel_args + [
                                            "-i", str(file), 
                                            "-i", str(p_img), 
                                            "-filter_complex", vf, 
                                            "-map", "[final_out]", 
                                            "-map", "0:a:0?" 
                                        ] + encoder_args + [str(nadir_vid)]
                                        
                                        self.log_message(f"       [NADIR] Using GPU Encoder: {encoder_name}", 'info')

                                    else:
                                        # === CPU ENCODER LOGIC  ===
                                        encoder_name = "libx265"
                                        encoder_args = [
                                            "-c:v", encoder_name, 
                                            "-preset", "veryfast", 
                                            "-crf", str(self.settings['NadirCRF']), 
                                            "-tag:v", "hvc1", 
                                            "-c:a", "copy"
                                        ]
                                        c_ov = [
                                            self.settings['FFmpegPath'], "-y", 
                                            "-i", str(file), 
                                            "-i", str(p_img), 
                                            "-filter_complex", vf, 
                                            "-map", "[final_out]", 
                                            "-map", "0:a:0?" 
                                        ] + encoder_args + [str(nadir_vid)]
                                        self.log_message(f"       [NADIR] Using CPU Encoder (libx265).", 'info')
                                    
                                    if self.run_command(c_ov, error_message="FFmpeg Overlay failed (Check GPU/CRF settings)")[0] == 0:
                                        input_video_mux = nadir_vid; is_nadir = True
                                        
                                        used_quality = self.settings['NadirQP'] if self.settings['UseGPUEncoding'] else self.settings['NadirCRF']
                                        quality_type = "QP" if self.settings['UseGPUEncoding'] else "CRF"
                                        
                                        self.log_message(f"       [NADIR] Applied. Output: {bit_depth}-bit, Quality {used_quality} ({quality_type})", 'success')
                                    else: 
                                        self.log_message(f"       [NADIR] FFmpeg Overlay failed with {encoder_name}. Please try CPU encoding.", 'error')
                                else: 
                                    self.log_message("       [NADIR] Magick failed. Patch skipped.", 'error')
                            else: 
                                self.log_message("       [NADIR] No dims. Patch skipped.", 'error')
                        
                        if not gpmf_source_path.exists():
                            self.log_message(f"    [WARNING] GPMF track missing for {file.name}.", 'warning'); continue
                        
                        if is_nadir:
                            cmd = [self.settings['FFmpegPath'], "-i", str(input_video_mux), "-i", str(gpmf_source_path), "-map", "0", "-map", "1", "-c", "copy", str(final_output_path), "-y"]
                        else:
                            cmd = [
                                self.settings['FFmpegPath'], 
                                "-i", str(file), 
                                "-i", str(gpmf_source_path), 
                                "-map", "0", 
                                "-map", "-0:3", 
                                "-map", "1", 
                                "-c", "copy", 
                                str(final_output_path), "-y"
                            ]

                        if self.run_command(cmd)[0] == 0:
                            self.log_message(f"    [SUCCESS] Muxed to {final_output_path.name}.", 'success')
                        
                        try: os.remove(gpmf_source_path) 
                        except: pass

                if nadir_work.exists(): shutil.rmtree(nadir_work, ignore_errors=True)

                # --- 3. METADATA CORRECTION ---
                step_counter += 1
                self.check_for_abort("Metadata Correction")
                self.log_message(f"\n[STEP {step_counter}/10] Transferring metadata...", 'info')

                intermediate_mov_files = list(Path(self.settings['TargetDir']).glob("*_gpmf_final.mov"))
                total_files = len(intermediate_mov_files)
                self.update_progress(0, total_files)
                
                if total_files > 0:
                    for i, video_file in enumerate(intermediate_mov_files, 1):
                        self.check_for_abort("Metadata Correction loop")
                        self.update_progress(i, total_files)
                        
                        temp_stem = video_file.stem.removesuffix('_gpmf_final')
                        original_base_name_candidate = temp_stem.removesuffix(custom_suffix)
                        original_360_path = Path(self.settings['SourceDir']) / f"{original_base_name_candidate}.360"
                        
                        if not original_360_path.exists(): continue
                        
                        command = [
                            self.settings['ExifToolPath'], '-TagsFromFile', str(original_360_path), 
                            '-time:all>time:all', '-GPSDateTime<GPSDateTime', '-Track*Date>Track*Date', 
                            '-P', '-overwrite_original', str(video_file)
                        ]
                        if self.run_command(command)[0] == 0:
                            self.log_message(f"    -> Metadata transferred for {video_file.name}.", 'success')
                else:
                    self.log_message(f"\n[INFO] Step 3 SKIPPED (No files).", 'info')

            else:
                step_counter = 3
                self.log_message(f"\n[INFO] Steps 1-3 SKIPPED.", 'info')


            # ==============================================================================
            # PHASE 2: CHANNEL SPLIT - Strictly separating Max 1 and Max 2 processing logic here.
            # ==============================================================================
            svs_fix_success = False
            
            # --- STEP 4: CHANNEL A: MAX 1 MP4 EXPORT ---
            if cam_model == 'Max 1':
                step_counter = 4
                self.check_for_abort("Max 1 MP4 Export")
                self.log_message(f"\n[STEP {step_counter}/10] Max 1 CHANNEL: Creating MP4 files (Copy Mode)...", 'info')
                
                intermediate_mov_files = list(Path(self.settings['TargetDir']).glob("*_gpmf_final.mov"))
                total_files = len(intermediate_mov_files)
                self.update_progress(0, total_files)
                
                for i, file in enumerate(intermediate_mov_files, 1):
                    self.check_for_abort("Max 1 MP4 Export loop")
                    self.update_progress(i, total_files)
                    
                    base_name = file.stem
                    clean_name = base_name.replace('_gpmf_final', '')
                    if self.settings['RunNadirPatch']: clean_name += NADIR_SUFFIX
                    target_mp4 = Path(self.settings['TargetDir']) / f"{clean_name}.mp4"
                    
                    self.log_message(f"    -> Copying to: {target_mp4.name}", 'info')
                    try:
                        shutil.copy2(file, target_mp4)
                    except Exception as e:
                        self.log_message(f"    [ERROR] Copy failed: {e}", 'error')
                
                # Explicitly skip SVS Steps (5 and 6) for Max 1
                self.log_message(f"\n[INFO] Max 1 detected: Skipping Steps 5 & 6 (Max 2 exclusive).", 'info')
                step_counter = 6 # Jump directly to Mapillary Sampling (Step 7)
                
            # --- CHANNEL B: MAX 2 PROCESSING ---
            elif cam_model == 'Max 2':
                svs_fix_success = False 
                
                # STEP 5: GPX GENERATION
                if self.settings['RunCorePrep'] and self.settings['RunGPX']:
                    step_counter = 5 
                    self.check_for_abort("GPX Generation")
                    self.log_message(f"\n[STEP {step_counter}/10] Max 2 CHANNEL: Generating GPX files (SVS Prep)...", 'info') 
                    
                    intermediate_mov_files = list(Path(self.settings['TargetDir']).glob("*_gpmf_final.mov"))
                    total_files = len(intermediate_mov_files)
                    self.update_progress(0, total_files)

                    for i, video_file in enumerate(intermediate_mov_files, 1):
                        self.check_for_abort("GPX Generation loop")
                        self.update_progress(i, total_files)
                        
                        self.log_message(f"    -> Generating GPX for file {i}/{total_files}: {video_file.name}", 'info')
                        temp_stem = video_file.stem.removesuffix('_gpmf_final')
                        final_output_base_name = temp_stem.removesuffix(custom_suffix)
                        gpx_output_path = Path(self.settings['SourceDir']) / f"{final_output_base_name}.gpx" 
                        
                        command = [ self.settings['ExifToolPath'], '-p', self.settings['GpxFormatPath'], '-ee', '-m', str(video_file) ]
                        return_code, output = self.run_command(command, error_message="ExifTool GPX generation failed")
                        
                        if return_code == 0 and "<gpx" in output and len(output) > 100: 
                            try:
                                with open(gpx_output_path, 'w', encoding='utf-8') as f: 
                                    f.write(output)
                                self.log_message(f"    [SUCCESS] GPX saved: {gpx_output_path.name}", 'success')
                            except Exception as e: 
                                self.log_message(f"    [ERROR] Error saving GPX: {e}", 'error')
                        else: 
                            self.log_message(f"    [ERROR] GPX generation failed for {video_file.name}.", 'error')
                else:
                    self.log_message(f"\n[STEP 5/10] GPX Generation SKIPPED.", 'info')

                # STEP 6: SVS HEADER FIX
                if self.settings['RunCorePrep'] and self.settings['RunSVSHeaderFix'] and self.settings['RunGPX']:
                    step_counter = 6
                    self.check_for_abort("SVS Header Fix")
                    self.log_message(f"\n[STEP {step_counter}/10] Max 2 CHANNEL: Fixing SVS MP4 Header Timestamps (from GPX)", 'info')
                    
                    output_dir = Path(self.settings['TargetDir']) / "SVS_Fixed_Headers"
                    output_dir.mkdir(exist_ok=True, parents=True)
                    self.log_message(f"    [INFO] Fixed files will be saved to: {output_dir.name}", 'info')
                    
                    gpx_files_in_source = list(Path(self.settings['SourceDir']).glob("*.gpx"))
                    total_files = len(gpx_files_in_source)
                    self.update_progress(0, total_files)
                    
                    files_fixed_count = 0

                    if total_files == 0:
                         self.log_message("    [WARNING] No GPX files found. Cannot run SVS Header Fix.", 'warning')
                    
                    for i, gpx_path in enumerate(gpx_files_in_source, 1):
                        self.check_for_abort("SVS Fix loop")
                        self.update_progress(i, total_files)

                        self.log_message(f"    -> Processing SVS Fix for file {i} of {total_files}: {gpx_path.name}", 'info')
                        
                        original_base_name = gpx_path.stem
                        
                        # Find the MOV in the TargetDir (with suffix)
                        mov_name = f"{original_base_name}{custom_suffix}_gpmf_final.mov"
                        source_video = Path(self.settings['TargetDir']) / mov_name
                        
                        if not source_video.exists():
                            self.log_message(f"    [ERROR] Source MOV not found. Skipping SVS Fix for {gpx_path.name}.", 'error')
                            continue
                        
                        # Determine final names in SVS_Fixed_Headers folder
                        svs_file_name_stem = f"{original_base_name}{custom_suffix}"
                        if self.settings['RunNadirPatch']:
                            svs_file_name_stem += NADIR_SUFFIX 
                        svs_file_name_stem += "_SVS" 

                        fixed_mp4_path = output_dir / f"{svs_file_name_stem}.mp4"
                        fixed_gpx_path = output_dir / f"{svs_file_name_stem}.gpx" 
                        
                        try:
                            # 1. Strip MOV of metadata tracks to create CLEAN SVS MP4 (uses GPX)
                            self.log_message(f"       [SVS FIX] Stripping internal metadata tracks to ensure GPX usage...", 'info')
                            cmd_strip = [
                                self.settings['FFmpegPath'], "-y",
                                "-i", str(source_video),
                                "-map", "0:v", "-map", "0:a?", # Copy video and optional audio, ignore data/gpmf tracks
                                "-c", "copy",
                                str(fixed_mp4_path) 
                            ]
                            if self.run_command(cmd_strip, error_message="SVS MP4 creation failed")[0] != 0:
                                self.log_message(f"    [ERROR] FFmpeg MP4 creation failed. Skipping fix.", 'error')
                                continue
                            
                            # 2. Copy GPX
                            shutil.copy2(gpx_path, fixed_gpx_path)

                        except Exception as e:
                            self.log_message(f"    [ERROR] Could not prepare files for SVS_Fixed_Headers folder: {e}", 'error')
                            continue
                            
                        # 3. Get GPX time
                        gpx_utc_time, exiftool_time = self._get_first_gpx_time_for_fixer(fixed_gpx_path)
                        
                        if not exiftool_time:
                            self.log_message(f"    [ERROR] Could not get GPX time. Skipping fix.", 'error')
                            continue
                            
                        # 4. ExifTool Fix command (with 6 data fields)
                        exiftool_args_fix = [
                            self.settings['ExifToolPath'],
                            "-m", 
                            f"-QuickTime:CreateDate={exiftool_time}",
                            f"-QuickTime:ModifyDate={exiftool_time}",
                            f"-QuickTime:TrackCreateDate={exiftool_time}",
                            f"-QuickTime:TrackModifyDate={exiftool_time}",
                            f"-QuickTime:MediaCreateDate={exiftool_time}",
                            f"-QuickTime:MediaModifyDate={exiftool_time}",
                            "-FileModifyDate<MediaModifyDate", 
                            "-overwrite_original_in_place",
                            str(fixed_mp4_path)
                        ]
                        
                        fix_code, _ = self.run_command(exiftool_args_fix, error_message="ExifTool SVS Header Fix failed")
                        
                        if fix_code == 0 or fix_code == 1: 
                            self.log_message("    [SUCCESS] ExifTool header fix applied.", 'success')
                            files_fixed_count += 1
                        else:
                            self.log_message(f"    [WARNING] ExifTool fix command returned an error (code {fix_code}). Proceeding to verification.", 'warning')

                        # 5. Verification
                        exiftool_args_verify = [
                            self.settings['ExifToolPath'],
                            "-QuickTime:CreateDate", "-QuickTime:ModifyDate",
                            "-QuickTime:TrackCreateDate", "-QuickTime:TrackModifyDate",
                            "-QuickTime:MediaCreateDate", "-QuickTime:MediaModifyDate",
                            str(fixed_mp4_path)
                        ]
                        
                        verify_code, verification_output = self.run_command(exiftool_args_verify, error_message="ExifTool SVS Verification failed")
                        
                        log_content = self._generate_verification_log(gpx_utc_time, verification_output, exiftool_time)
                        self.log_message(f"    [VERIFICATION LOG]\n{log_content}", 'info')
                    
                    if files_fixed_count > 0:
                        svs_fix_success = True
                else:
                    self.log_message(f"\n[STEP 6/10] SVS Header Fix SKIPPED.", 'info')

            # If Max 1 was executed (or steps skipped), ensure counter is set for Mapillary steps
            if cam_model == 'Max 1' and step_counter < 6:
                 step_counter = 6

            # ==============================================================================
            # PHASE 3: MAPILLARY PROCESSING
            # ==============================================================================

            # --- MAPILLARY STEPS ---
            if self.settings['RunCorePrep'] and (self.settings['RunSample'] or self.settings['RunProcess']):
                if self.settings['RunSample']:
                    step_counter += 1
                    self.check_for_abort("Mapillary Sampling")
                    self.log_message(f"\n[STEP {step_counter}/10] Sampling video frames...", 'info')
                    
                    intermediate_mov_files = list(Path(self.settings['TargetDir']).glob("*_gpmf_final.mov"))
                    total_files = len(intermediate_mov_files)
                    self.update_progress(0, total_files)
                    
                    for i, video_file in enumerate(intermediate_mov_files, 1):
                        self.check_for_abort("Mapillary Sampling loop")
                        self.update_progress(i, total_files)
                        
                        self.log_message(f"    -> Sampling: {video_file.name}", 'info')
                        
                        sampling_args = [
                            self.settings['MapillaryToolsPath'], 
                            "sample_video", 
                            str(video_file), 
                            str(temp_mapillary_dir), 
                            f"--video_sample_distance={self.settings['VideoSampleDistance']}"
                        ]
                        
                        # Add nadir patch logic if enabled
                        if self.settings['RunNadirPatch'] and self.settings['NadirImagePath']:
                             pass

                        self.run_command(sampling_args, error_message="Mapillary Sampling failed")
                else:
                     step_counter += 1
                     self.log_message(f"\n[STEP {step_counter}/10] Mapillary Sampling SKIPPED.", 'info')
                
                if self.settings['RunProcess']:
                    step_counter += 1
                    self.check_for_abort("Mapillary Processing")
                    self.log_message(f"\n[STEP {step_counter}/10] Processing sampled frames...", 'info')
                    
                    if temp_mapillary_dir.exists():
                        # Process the frames (add geotags/sequences)
                        process_args = [
                            self.settings['MapillaryToolsPath'], 
                            "process", 
                            str(temp_mapillary_dir)
                        ]
                        
                        self.run_command(process_args, error_message="Mapillary Processing failed")

                    else:
                        self.log_message("    [WARNING] No frames directory found to process.", 'warning')

                else:
                     step_counter += 1
                     self.log_message(f"\n[STEP {step_counter}/10] Mapillary Processing SKIPPED.", 'info')
            else: 
                 step_counter = max(step_counter, 8)

            # --- STEP 9: UPLOAD ---
            step_counter = max(step_counter, 8) + 1 # Becomes 9
            if self.settings['RunUpload']:
                self.check_for_abort("Mapillary Upload")
                self.log_message(f"\n[STEP {step_counter}/10] Uploading to Mapillary...", 'info')

                root_desc_file = temp_mapillary_dir / "mapillary_image_description.json"

                # SITUATION 1: JSON is in the root directory
                if root_desc_file.exists():
                     self.log_message(f"    [INFO] Global description file found in root. Uploading entire batch...", 'info')
                     
                     user_arg = self.settings.get('MapillaryUser', self.settings.get('MapillaryUserName', ''))
                     
                     upload_args = [
                            self.settings['MapillaryToolsPath'], 
                            "upload", 
                            "--user_name", user_arg, 
                            str(temp_mapillary_dir) 
                        ]
                     
                     exit_code, output = self.run_command(upload_args)
                     if exit_code != 0:
                         self.log_message(f"    [ERROR] Upload failed. Check the logs above.", 'error')
                     else:
                         self.log_message(f"    [SUCCESS] Batch upload completed.", 'success')

                # SITUATION 2: No JSON in root, checking individual subfolders (Fallback)
                elif temp_mapillary_dir.exists():
                    self.log_message(f"    [INFO] No root JSON found. Checking individual subfolders...", 'info')
                    
                    seq_dirs = [d for d in temp_mapillary_dir.iterdir() if d.is_dir()]
                    total_seq = len(seq_dirs)
                    
                    if total_seq == 0:
                        self.log_message(f"    [WARNING] No folders found in {temp_mapillary_dir.name}.", 'warning')

                    for i, seq_dir in enumerate(seq_dirs, 1):
                        self.check_for_abort("Mapillary Upload loop")
                        
                        # Check if a JSON exists in the SUBFOLDER
                        if not (seq_dir / "mapillary_image_description.json").exists():
                             self.log_message(f"    [WARNING] Skipping {seq_dir.name}: No description file found.", 'warning')
                             continue

                        self.log_message(f"    -> Uploading sequence: {seq_dir.name}...", 'info')
                        
                        user_arg = self.settings.get('MapillaryUserName', '')
                        upload_args = [
                            self.settings['MapillaryToolsPath'], "upload", 
                            "--user_name", user_arg, 
                            str(seq_dir)
                        ]
                        self.run_command(upload_args)
                else:
                    self.log_message(f"    [ERROR] Mapillary output directory not found.", 'error')
            else:
                 self.log_message(f"\n[STEP {step_counter}/10] Mapillary Upload SKIPPED.", 'info')

            # --- 10. FINAL CLEANUP ---
            step_counter += 1
            self.check_for_abort("Final Cleanup")
            self.update_progress(100, 100)
            self.log_message(f"\n[STEP {step_counter}/10] Final cleanup and renaming...", 'info')
            
            # B. Remove GPX files from SourceDir (only for Max 2 SVS workflow, if GPX was executed)
            cam_model = self.settings.get('CameraModel', 'Unknown')
            if cam_model == 'Max 2' and self.settings.get('RunGPX', False):
                gpx_files_to_clean = list(Path(self.settings['SourceDir']).glob("*.gpx"))
                if gpx_files_to_clean:
                    self.log_message(f"    -> Cleaning up {len(gpx_files_to_clean)} GPX files from Source Directory...", 'info')
                    for f in gpx_files_to_clean:
                        try:
                            os.remove(f)
                            self.log_message(f"    [INFO] Removed GPX file: {f.name} from SourceDir.", 'success')
                        except Exception as e:
                            self.log_message(f"    [WARNING] Could not delete GPX file {f.name}: {e}", 'warning')
                else:
                    self.log_message(f"    -> No GPX files found in SourceDir to clean.", 'info')

            # A. ALWAYS remove intermediate _gpmf_final.mov files
            mov_files_to_clean = list(Path(self.settings['TargetDir']).glob("*_gpmf_final.mov"))
            if mov_files_to_clean:
                self.log_message(f"    -> Cleaning up {len(mov_files_to_clean)} intermediate .mov files...", 'info')
                for f in mov_files_to_clean:
                    try:
                        os.remove(f)
                        self.log_message(f"    [INFO] Removed intermediate MOV file: {f.name}", 'success')
                    except Exception as e:
                        self.log_message(f"    [WARNING] Could not delete {f.name}: {e}", 'warning')
            else:
                self.log_message(f"    -> No intermediate .mov files found to clean.", 'info')

            # C. Rename Mapillary Folders (with Max 1/2 logic)
            if temp_mapillary_dir.exists() and (self.settings['RunProcess'] or self.settings['RunUpload']):
                self.log_message(f"    [INFO] Mapillary processing complete. Renaming sequences by removing workflow suffixes...", 'info')
                
                temp_sequence_dirs = [d for d in temp_mapillary_dir.iterdir() if d.is_dir()]
                
                for seq_dir in temp_sequence_dirs:
                    original_name = seq_dir.name
                    new_name = original_name
                    
                    # 1. Remove workflow suffix
                    if '_gpmf_final' in new_name:
                        new_name = new_name.replace('_gpmf_final', '')
                        
                    # 2. Ensure .mov extension is gone
                    if new_name.endswith('.mov'):
                        new_name = new_name[:-4] 
                    
                    final_seq_name = new_name 

                    # 3. Add Nadir suffix if applicable
                    if self.settings['RunNadirPatch'] and NADIR_SUFFIX not in final_seq_name:
                        final_seq_name += NADIR_SUFFIX
                    
                    if final_seq_name != original_name and final_seq_name:
                        new_path = seq_dir.parent / final_seq_name
                        try:
                            seq_dir.rename(new_path)
                            self.log_message(f"    [SUCCESS] Renamed from '{original_name}' to '{new_path.name}'", 'success')
                        except Exception as e:
                            self.log_message(f"    [ERROR] Could not rename folder '{original_name}': {e}", 'error')
                    else:
                        self.log_message(f"    [INFO] Folder '{original_name}' left unchanged (no renaming required).", 'info')

                self.log_message(f"    [INFO] Frames location: {temp_mapillary_dir.name} folder in TargetDir.", 'info')
            else:
                 self.log_message(f"    [INFO] No Mapillary folders found to clean/rename.", 'info')

            # --- End Display ---
            end_time = datetime.now()
            elapsed_time = end_time - start_time 
            total_seconds = int(elapsed_time.total_seconds())
            hours = total_seconds // 3600
            minutes = (total_seconds % 3600) // 60
            seconds = total_seconds % 60
            formatted_time = f"{hours:02}:{minutes:02}:{seconds:02}" 
            
            final_summary_message = f"The GoPro Max video preparation workflow has finished.\nTotal Time: {formatted_time}"
            
            if self.settings['RunSVSHeaderFix'] and cam_model == 'Max 2' and svs_fix_success:
                svs_upload_dir = Path(self.settings['TargetDir']) / "SVS_Fixed_Headers"
                
                if svs_upload_dir.exists() and any(svs_upload_dir.iterdir()):
                     svs_message = (
                        "The **Streetview Studio-ready** The MP4 and GPX files can be"
                        f"found in the following map, ready for upload:\n\n"
                        f"**{svs_upload_dir}**"
                    )
                     
                     final_summary_message += (
                        f"\n\nStreetview Studio files save in:\n"
                        f"{svs_upload_dir.name} map in your Targetmap."
                    )

            self.log_message("\n=======================================================", 'success')
            self.log_message(f"  WORKFLOW COMPLETE! Time: {formatted_time}", 'success')
            self.log_message(f"=======================================================\n", 'success')
            
            messagebox.showinfo("Done", final_summary_message)

        except UserAbortException as e:
            self.log_message(f"\n[ABORTED] {e}", 'error')
            messagebox.showwarning("Aborted", "Workflow stopped by user.")
        except Exception as e:
            self.log_message(f"\n[FATAL ERROR] {e}", 'error')
            messagebox.showerror("Crash", str(e))
        finally:
            self._cleanup_after_workflow()
    
    def run_hero_workflow_logic(self):
        try:
            start_time = datetime.now()
            self.log_message("--- STARTING GOPRO HERO WORKFLOW ---", 'info')
            
            src = Path(self.settings['HeroSourceDir'])
            tgt = Path(self.settings['HeroTargetDir'])
            
            if not tgt.exists(): tgt.mkdir(parents=True)
            
            mp4_files = list(src.glob("*.mp4"))
            if not mp4_files:
                self.log_message("[ERROR] No .mp4 files found in Hero Source.", 'error')
                return
            
            total = len(mp4_files)
            upload_success_dir = tgt / "Upload_Successful"
            
            self.update_progress(0, total)

            for i, video in enumerate(mp4_files, 1):
                self.check_for_abort(f"Hero Video Loop ({video.name})")
                
                pct = self.update_progress(i, total)
                
                self.log_message(f"\nProcessing Hero Video {i}/{total} ({pct:.1f}%): {video.name}", 'info')
                
                # --- VARIABLE DEFINITIONS ---
                # 1. Determine temporary output directory name (default video name)
                temp_output_dir = tgt / video.stem
                
                # 2. Determine final directory name (including suffix)
                custom_suffix = f"_{self.settings['FileSuffix']}" if self.settings['FileSuffix'] else ""
                final_sequence_name = f"{video.stem}{custom_suffix}"
                final_target_path = tgt / final_sequence_name
                
                # By default, assume output is here:
                video_frames_dir = final_target_path 

                # --- STEP 1: SAMPLING ---
                self.check_for_abort(f"Hero Sampling ({video.name})")
                self.log_message(f"  -> Sampling...", 'info')
                
                # Mapillary tools command
                cmd_sample = [
                    self.settings['MapillaryToolsPath'], 
                    "sample_video", 
                    str(video), 
                    str(temp_output_dir), 
                    f"--video_sample_distance", str(self.settings['VideoSampleDistance'])
                ]
                
                c, _ = self.run_command(cmd_sample)
                if c != 0: continue
                
                # --- STEP 2: DIRECTORY STRUCTURE CORRECTION ---
                # Mapillary sometimes creates a subfolder 'GX01.MP4' inside 'GX01'. We flatten this.
                actual_sample_subfolder = temp_output_dir / video.name # e.g.: Target/GX01/GX01.MP4
                
                if actual_sample_subfolder.exists():
                    self.log_message(f"  -> Correcting nested directory structure...", 'info')
                    for item in actual_sample_subfolder.iterdir():
                        shutil.move(str(item), str(temp_output_dir / item.name))
                    shutil.rmtree(actual_sample_subfolder, ignore_errors=True)
                
                # Rename folder to version with Suffix (if needed)
                if temp_output_dir != final_target_path:
                    try:
                        if final_target_path.exists(): shutil.rmtree(final_target_path)
                        temp_output_dir.rename(final_target_path)
                        self.log_message(f"  -> Renamed folder to: {final_target_path.name}", 'info')
                    except Exception as e:
                        self.log_message(f"  [ERROR] Could not rename folder: {e}. Keeping original name.", 'error')
                        video_frames_dir = temp_output_dir # Fallback

                # --- STEP 3: PROCESSING ---
                self.check_for_abort(f"Hero Processing ({video.name})")
                self.log_message(f"  -> Processing frames in {video_frames_dir.name}...", 'info')
                cmd_process = [self.settings['MapillaryToolsPath'], "process", str(video_frames_dir)]
                c, _ = self.run_command(cmd_process)
                if c != 0: continue
                
                # --- STEP 4: UPLOAD (OPTIONAL) ---
                if self.settings['RunUpload']:
                    self.check_for_abort(f"Hero Upload ({video.name})")
                    self.log_message(f"  -> Uploading...", 'info')
                    cmd_upload = [
                        self.settings['MapillaryToolsPath'], "upload", 
                        str(video_frames_dir), 
                        "--user_name", self.settings['MapillaryUserName'], 
                        f"--num_upload_workers={self.settings['MapillaryUploadWorkers']}"
                    ]
                    c, _ = self.run_command(cmd_upload)
                    
                    # Move on success
                    if c == 0:
                        self.log_message(f"  -> Upload Success! Moving to {upload_success_dir.name}...", 'success')
                        upload_success_dir.mkdir(exist_ok=True)
                        try:
                            destination = upload_success_dir / video_frames_dir.name
                            if destination.exists(): shutil.rmtree(destination)
                            shutil.move(str(video_frames_dir), str(upload_success_dir))
                        except Exception as e:
                            self.log_message(f"  [WARNING] Move failed: {e}", 'warning')
                    else:
                        self.log_message(f"  [ERROR] Upload failed. Frames remain in {video_frames_dir.name}", 'error')

            elapsed = datetime.now() - start_time
            self.log_message(f"--- HERO WORKFLOW FINISHED ({elapsed}) ---", 'success')
            messagebox.showinfo("Done", "GoPro Hero Workflow Complete")

        except UserAbortException as e:
            self.log_message(f"\n[WORKFLOW ABORTED] {e}", 'error')
            messagebox.showwarning("Aborted", "The Hero Workflow was manually stopped.")
        except Exception as e:
            self.log_message(f"\n[FATAL ERROR] Hero workflow thread crashed: {e}", 'error')
            messagebox.showerror("Fatal Error", f"Hero workflow thread crashed:\n{e}")
        finally:
            self._cleanup_after_workflow()
        
if __name__ == "__main__":
    FIXED_BG_COLOR = '#E8E8E8' 
    ACTIVE_BG_COLOR = '#D8D8D8' 
    ORANGE_BUTTON_COLOR = '#EC9C4E'
    # NEW: Hover color (Teal)
    HOVER_BUTTON_COLOR = '#47A9A3'
    
    BUTTON_FONT = ('Arial', 10, 'bold')
    HEADER_FONT = ('Arial', 10, 'bold')

    try:
        root = tk.Tk()
        root.configure(bg=FIXED_BG_COLOR) 
        
        style = ttk.Style(root)
        try:
            style.theme_use('clam')
            
            # --- GENERAL TTK STYLING FIXES FOR BACKGROUND COLOR (#E8E8E8) ---
            style.configure('TFrame', background=FIXED_BG_COLOR) 
            style.configure('TLabelframe', background=FIXED_BG_COLOR)
            style.configure('TLabelframe.Label', font=HEADER_FONT, background=FIXED_BG_COLOR, foreground='black') 

            style.configure('TButton', font=BUTTON_FONT, background=ORANGE_BUTTON_COLOR, borderwidth=1, relief="raised")
            style.map('TButton', 
                      background=[('active', HOVER_BUTTON_COLOR), ('!disabled', ORANGE_BUTTON_COLOR)]) 
            
            # Workflow options
            style.configure('TRadiobutton', background=FIXED_BG_COLOR) 
            style.map('TRadiobutton',
                      background=[('disabled', FIXED_BG_COLOR), ('selected', FIXED_BG_COLOR), ('active', FIXED_BG_COLOR)],
                      foreground=[('disabled', 'grey')])
            
            style.configure('Bold.TRadiobutton', font=('Arial', 9, 'bold'))
            style.map('Bold.TRadiobutton',
                      background=[('disabled', FIXED_BG_COLOR), ('selected', FIXED_BG_COLOR), ('active', FIXED_BG_COLOR)],
                      foreground=[('disabled', 'grey')])

            style.configure('TCheckbutton', background=FIXED_BG_COLOR) 
            style.map('TCheckbutton',
                      background=[('disabled', FIXED_BG_COLOR), ('selected', FIXED_BG_COLOR), ('active', FIXED_BG_COLOR)])
            
            style.configure('TEntry', fieldbackground='white') 
            
            # TNotebook Styling
            style.configure('TNotebook', background=FIXED_BG_COLOR, borderwidth=0) 
            style.configure('TNotebook.Tab', background=FIXED_BG_COLOR, foreground='black', borderwidth=1, focuscolor=FIXED_BG_COLOR)
            style.map('TNotebook.Tab',
                        background=[('selected', FIXED_BG_COLOR), ('active', ACTIVE_BG_COLOR)], 
                        foreground=[('selected', 'black')]) 
            
            # --- START BUTTON: BIG & ORANGE (Font size 12 bold) ---
            style.configure('Accent.Big.TButton', 
                            font=('Arial', 12, 'bold'), 
                            foreground='black', 
                            background=ORANGE_BUTTON_COLOR, 
                            padding=[20, 11, 20, 11]) 
            style.map('Accent.Big.TButton', 
                       background=[('active', HOVER_BUTTON_COLOR), ('!disabled', ORANGE_BUTTON_COLOR)])

            # --- STOP BUTTON STYLE (Red) ---
            style.configure('Stop.TButton', 
                            font=BUTTON_FONT, 
                            background='red', 
                            foreground='white',
                            borderwidth=1, 
                            relief="raised")
            style.map('Stop.TButton', 
                       background=[('active', '#CC0000'), ('!disabled', 'red')],
                       foreground=[('active', 'white'), ('!disabled', 'white')])
            
            # --- PROGRESS BAR STYLE (Green on White) ---
            style.configure("Horizontal.TProgressbar",
                            troughcolor='white',      # Progress bar background (white)
                            background='#32CD32',     # The progress itself (bright green)
                            bordercolor='#999999',    # Border color
                            lightcolor='#32CD32',     # Shadow corrections for 3D effect
                            darkcolor='#32CD32',
                            thickness=20)             # Bar thickness (for visibility)
            # -------------------------------------------
            
        except Exception as e:
             print(f"Warning: Failed to apply ttk styling changes: {e}") 
        
        root.update_idletasks()
        
        app = MapillaryApp(root, FIXED_BG_COLOR)
        
        root.mainloop()
    except tk.TclError as e:
        error_msg = f"FATAL ERROR (Tcl/Tk): The graphical interface could not be started.\n\nSpecific Error:\n{e}\n\nEnsure Python is installed correctly."
        print(error_msg)
        try:
            import tkinter.messagebox
            root_err = tk.Tk()
            root_err.withdraw()
            tkinter.messagebox.showerror("Fatal Tcl/Tk Error", error_msg)
        except:
            pass
        sys.exit(1)
    except Exception as e:
        import traceback           
        traceback.print_exc()        
        print(f"\n\n[FATAL ERROR] The application crashed with an unexpected error.")
        print(f"Error Type: {type(e).__name__}")
        print(f"Error Message: {e}")
        try:
            tk.messagebox.showerror("Fatal Error", f"The application crashed with an unexpected error:\n{e}")
        except:
            pass
        sys.exit(1)