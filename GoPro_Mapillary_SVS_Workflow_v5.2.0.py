# -------------------------------------------------------------------------
# SCRIPT NAME: GoPro_Mapillary_SVS_Workflow_v5.2.0.py
# VERSION: 5.2.0
# AUTHOR: Michel Faken
# DESCRIPTION: Comprehensive workflow tool for processing GoPro video files for Mapillary and Streetview Studio (SVS).
#              It handles Max 360 footage (10-step Max 1/2 logic, Nadir, SVS Fixes) and
#              GoPro Hero standard video footage (Mapillary sampling/processing/upload logic).
# -------------------------------------------------------------------------

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import os
import sys
import json
import hashlib
import time
import re
import math
from datetime import datetime, timedelta
from pathlib import Path
import subprocess
import shutil
import threading
import queue 
import xml.etree.ElementTree as ET
import webbrowser 

APP_VERSION = "5.2.0"
SPLASH_MAX_MS = 10000
SPLASH_MIN_MS = 2000
SPLASH_IMAGE = "Banner.png"

# --- Workflow step labels ---
STEP_LABEL_SVS_FIX = "Max 2 CHANNEL: Fixing SVS MP4 header timestamps (from GPX)"
STEP_LABEL_GPX = "Max 2 CHANNEL: Generating GPX files (SVS Prep)"

STEP_LABEL_SAMPLE = "Sampling video frames"
STEP_LABEL_PROCESS = "Processing frames with Mapillary Tools"
STEP_LABEL_UPLOAD = "Uploading to Mapillary"
STEP_LABEL_MUX = "Muxing detected source video and GPMF (.mov)"

# --- Common skip reasons ---
SKIP_REASON_MAPILLARY_DISABLED = "Mapillary phase disabled"
SKIP_REASON_SAMPLING_DISABLED = "Sampling disabled"
SKIP_REASON_PROCESSING_DISABLED = "Processing disabled"
SKIP_REASON_UPLOAD_DISABLED = "Upload disabled"
SKIP_REASON_CORE_PREP_DISABLED = "Core Prep disabled"
SKIP_REASON_NO_MAX2_ITEMS = "No Max 2 items detected"
SKIP_REASON_TIMEWARP_MAPILLARY_DEFERRED = "TimeWarp items temporarily excluded from Mapillary"

# --- Imports for Logo ---
from PIL import Image, ImageTk

# --- User Abort Control Class ---
class UserAbortException(Exception):
    """Custom exception raised when the user manually aborts the workflow."""
    pass

# --- Windows specific flag to suppress pop-up windows ---
CREATE_NO_WINDOW = 0x08000000
# --- Windows process priority classes ---
NORMAL_PRIORITY_CLASS = 0x00000020
BELOW_NORMAL_PRIORITY_CLASS = 0x00004000 

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

def show_splash(root, version_text, max_ms=10000, bg_color="#E8E8E8", image_name="Banner.png"):
    """
    Splashscreen met banner + versie + dynamische 'Loading...'.
    Sluit automatisch na max_ms, maar kan eerder gesloten worden via returned close().
    """
    splash = tk.Toplevel(root)
    splash.overrideredirect(True)
    splash.configure(bg=bg_color)

    # Schermmaat
    splash.update_idletasks()
    sw = splash.winfo_screenwidth()
    sh = splash.winfo_screenheight()

    # Max banner grootte (percentage van scherm) - tweakbaar
    max_w = int(sw * 0.50)  # Was 0.70
    max_h = int(sh * 0.25)  # Was 0.45

    # Banner laden (referentie vasthouden!)
    splash.banner_img = None
    try:
        img_path = resource_path(image_name)
        img = Image.open(img_path)

        img_w, img_h = img.size
        scale = min(max_w / img_w, max_h / img_h, 1.0)

        new_w = int(img_w * scale)
        new_h = int(img_h * scale)

        if scale < 1.0:
            img = img.resize((new_w, new_h), Image.LANCZOS)

        splash.banner_img = ImageTk.PhotoImage(img)
    except Exception as e:
        splash.banner_img = None
        print(f"[WARNING] Splash image load failed: {e}", file=sys.stderr)

    # Layout
    container = tk.Frame(splash, bg=bg_color, padx=22, pady=18)
    container.pack(fill="both", expand=True)

    if splash.banner_img:
        tk.Label(container, image=splash.banner_img, bg=bg_color).pack(pady=(0, 10))

    tk.Label(
        container,
        text=f"Version {version_text}",
        font=("Arial", 11, "bold"),
        bg=bg_color,
        fg="#333333"
    ).pack()

    # Dynamische loading tekst
    loading_var = tk.StringVar(value="Loading")
    tk.Label(
        container,
        textvariable=loading_var,
        font=("Arial", 10),
        bg=bg_color,
        fg="#555555"
    ).pack(pady=(8, 6))

    splash._dot_step = 0
    splash._anim_after = None
    splash._close_after = None
    splash._closed = False

    def animate_dots():
        if splash._closed or not splash.winfo_exists():
            return
        splash._dot_step = (splash._dot_step + 1) % 4
        loading_var.set("Loading" + "." * splash._dot_step)
        splash._anim_after = splash.after(250, animate_dots)

    def close():
        """Closes the splash safely; can be called multiple times."""
        if splash._closed:
            return
        splash._closed = True

        try:
            if splash._anim_after:
                splash.after_cancel(splash._anim_after)
        except tk.TclError as e:
            print(f"[WARNING] Splash animation cancel failed: {e}", file=sys.stderr)

        try:
            if splash._close_after:
                splash.after_cancel(splash._close_after)
        except tk.TclError as e:
            print(f"[WARNING] Splash close timer cancel failed: {e}", file=sys.stderr)

        try:
            splash.destroy()
        except tk.TclError as e:
            print(f"[WARNING] Splash destroy failed: {e}", file=sys.stderr)

    animate_dots()

    # Centreren
    splash.update_idletasks()
    w = splash.winfo_width()
    h = splash.winfo_height()
    x = (sw - w) // 2
    y = (sh - h) // 2
    splash.geometry(f"{w}x{h}+{x}+{y}")

    # --- Close splash if user alt-tabs away / window loses focus ---
    try:
        splash.bind("<FocusOut>", lambda e: close())
        splash.bind("<Unmap>", lambda e: close())
        splash.bind("<Escape>", lambda e: close())
    except tk.TclError as e:
        print(f"[WARNING] Splash bind failed: {e}", file=sys.stderr)

    # Fallback: altijd sluiten na max_ms
    splash._close_after = splash.after(max_ms, close)

    return close

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

## --- Global Constants ---
NADIR_SUFFIX = "_nadir"
TIMEWARP_SVS_GPX_DIR_NAME = "SVS_TimeWarp_GPX"

## --- Global Constants for GPX fix ---
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
        except tk.TclError:
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
        
        master.title("GoPro Max & Hero - Mapillary & SVS Workflow Tool (V5.2.0)")
        
        master.resizable(True, True) 
        master.minsize(width=850, height=1000) 
        
        self.nadir_cache_lock = threading.Lock()
        self._tls = threading.local()

        # --- Load Logo ---
        self.logo_image = None  
        try:
            logo_path = resource_path("Banner_side.png")
            if logo_path.exists():
                pil_image = Image.open(logo_path)
                pil_image.thumbnail((403, 150)) 
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

        # 3. Define File Paths (Files are created later, after settings load)
        timestamp_filename = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.log_file_path = os.path.join(logs_std_dir, f"Workflow_Log_{timestamp_filename}.txt")
        self.log_file_extended_path = os.path.join(logs_ext_dir, f"Workflow_Log_{timestamp_filename}_extended.txt")

        # ... (Start variable initialization) ...
        self.log_text = None
        self.log_text_extended = None

        # --- Settings Dictionary ---
        self.settings = {
            'SourceDir': "", 'TargetDir': "", 'UtilityPath': "", 'ExifToolPath': "",
            'FFmpegPath': "", 'FFprobePath': "", 'MapillaryToolsPath': "", 'GpxFormatPath': "",
            'ImageMagickPath': "", 'NadirImagePath': "", 'NadirScaleFactor': 0.2500,
            'MapillaryUserName': "", 'VideoSampleDistance': 3.0, 'FileSuffix': "",
            'MapillaryUploadWorkers': 8,
            'ParallelNadirJobs': 1,
            'FFmpegPriority': 'belownormal',
            'RunCorePrep': False, 'RunGPX': False, 'RunSVSHeaderFix': False, 'RunSample': False,
            'RunProcess': False, 'RunUpload': False, 'RunNadirPatch': False,
            'SaveStandardLog': True, 'SaveExtendedLog': True,
            'CineformCRF': 15, 'CineformQP': 16,
            'TotalVideosProcessed': 0, 'TotalImagesProcessed': 0, 'StartTime': None,
            'CameraModel': 'Max 2', 
            'UseGPUEncoding': True,
            'GPUEncoder': 'auto',
            'NadirCRF': 17,
            'NadirQP': 18,
            'HeroSourceDir': "",
            'HeroTargetDir': "",
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
        self.nadir_scale_var = tk.DoubleVar(value=0.250)
        self.nadir_crf_var = tk.IntVar(value=17)
        self.run_nadir_patch_var = tk.BooleanVar(value=False)
        today_suffix = datetime.now().strftime("%d%m%Y")
        self.file_suffix_var = tk.StringVar(value=today_suffix)
        self.workflow_choice = tk.IntVar(value=1)
        self.mapillary_actions_var = tk.IntVar(value=1)
        self.hero_mapillary_actions_var = tk.IntVar(value=1)
        self.use_gpu_encoding_var = tk.BooleanVar(value=False)
        self.gpu_encoder_var = tk.StringVar(value='auto')
        self.nadir_qp_var = tk.IntVar(value=18)
        self.cineform_crf_var = tk.IntVar(value=15)
        self.cineform_qp_var = tk.IntVar(value=16)
        self.camera_model_var = tk.StringVar(value='Max 2')
        self.dir_entries = {}
        self.auto_follow_var = tk.BooleanVar(value=True)
        self._log_user_scrolling = set()       
        self._log_follow_tail = {}              
        self._log_scroll_after_ids = {}         

        self._log_scroll_lock = set()
        self.log_text = None
        self.log_text_extended = None
        self.save_std_log_var = tk.BooleanVar(value=True)
        self.save_ext_log_var = tk.BooleanVar(value=True)     
        self.tool_versions = {}
        self.stop_event = threading.Event()
        self.running_thread = None 
        self.stop_button = None
        self.progress_bar = None
        self.ui_queue = queue.Queue()

        # Temporary per-run metadata/probe caches
        # Prevents repeated exiftool / ffprobe calls within the same workflow run
        self._analysis_cache = {
            'ffprobe': {},
            'exiftool_json': {}
        }
        
        # --- Main UI Structure ---
        self.notebook = ttk.Notebook(master)
        self.notebook.pack(pady=10, padx=10, expand=True, fill='both')

        # Create Tabs
        self.config_tab = ttk.Frame(self.notebook)
        self.max_tab = ttk.Frame(self.notebook)       
        self.hero_tab = ttk.Frame(self.notebook)  
        self.log_tab = ttk.Frame(self.notebook) 
        self.log_tab_extended = ttk.Frame(self.notebook)
        self.about_tab = ttk.Frame(self.notebook) 

        self.notebook.add(self.config_tab, text='Configuration')
        self.notebook.add(self.max_tab, text='GoPro Max Workflow')
        self.notebook.add(self.hero_tab, text='GoPro Hero Workflow')
        self.notebook.add(self.log_tab, text='Output Log')
        self.notebook.add(self.log_tab_extended, text='Output Log - Extended')
        self.notebook.add(self.about_tab, text='About / Help') 
        
        # --- Time mode analysis state ---
        self.detected_timewarp_items = []
        self.unsupported_time_mode_items = []
        
        if not hasattr(self, 'parallel_nadir_jobs_var'):
            self.parallel_nadir_jobs_var = tk.IntVar(value=1)  # load_settings() 

        # 1. Create Log Content
        self.create_log_tab_content(self.log_tab) 
        self.create_log_extended_tab_content(self.log_tab_extended)

        # Define the config file path
        self.config_file = SETTINGS_FILE_PATH

        # 2. Load settings
        settings_loaded_successfully = self.load_settings()
        
        # --- Initialize Log Files (Based on loaded settings) ---
        try:
            # Initialize Standard Log File (ONLY IF ENABLED)
            if self.save_std_log_var.get():
                with open(self.log_file_path, "w", encoding="utf-8") as f:
                    f.write(f"--- Workflow Log Started: {timestamp_filename} ---\n")
                    f.write("--- Script Version: 5.2.0 ---\n\n")
            
            # Initialize Extended Log File (ONLY IF ENABLED)
            if self.save_ext_log_var.get():
                with open(self.log_file_extended_path, "w", encoding="utf-8") as f:
                    f.write(f"--- Extended Workflow Log Started: {timestamp_filename} ---\n")
                    f.write("--- Contains full output from external tools (FFmpeg, ExifTool, Mapillary) ---\n\n")
        except Exception as e:
            print(f"Error creating log file: {e}")
        
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
        
        self.master.after(100, self._process_ui_queue)
    
    @staticmethod
    def run_exiftool_normal_priority(cmd, logger):
        """
        Runs ExifTool with NORMAL_PRIORITY_CLASS on Windows to prevent IO starvation
        when the main workflow or FFmpeg runs at reduced priority.

        On non-Windows platforms, the command is executed without Windows-specific
        creation flags.
        """
        popen_kwargs = {
            "stdout": subprocess.PIPE,
            "stderr": subprocess.PIPE,
            "text": True,
        }

        if os.name == 'nt':
            popen_kwargs["creationflags"] = CREATE_NO_WINDOW | NORMAL_PRIORITY_CLASS

        logger.info("[EXIFTOOL] Launching ExifTool with normal priority...")

        result = subprocess.run(cmd, **popen_kwargs)

        if result.returncode != 0:
            logger.error("[EXIFTOOL] ExifTool failed.")
            if result.stderr:
                logger.error(result.stderr.strip())
            raise RuntimeError("ExifTool execution failed")

        if result.stdout:
            logger.debug(result.stdout.strip())

        logger.info("[EXIFTOOL] ExifTool finished successfully.")
    
    # ============================================
    # LOGGING HELPERS
    # ===========================================
    def _normalize_log_message(self, message):
        """
        Normalizes a log message and returns:
        (clean_message, add_newline_before)
        """
        add_newline = False
        if message.startswith("\n"):
            add_newline = True
            message = message.lstrip("\n")
        return message, add_newline


    def _determine_log_tag(self, message, message_type='info'):
        """
        Determines the log tag for Tkinter text widgets.
        """
        if message_type == 'cmd':
            return 'cmd'
            
        # Allow direct tag mapping for nadir process channels
        if isinstance(message_type, str) and message_type.startswith('nadir_p'):
            return message_type
            return


        msg_lower = message.lower()

        if message_type == 'error' or 'error' in msg_lower or 'problem' in msg_lower or 'fatal' in msg_lower:
            return 'error'
        elif message_type == 'success' or 'success' in msg_lower or 'complete' in msg_lower:
            return 'success'
        elif message_type == 'warning' or 'warning' in msg_lower:
            return 'warning'
        else:
            return 'info'


    def _format_log_message(self, message):
        """
        Formats the message with a timestamp and returns the final log line.
        """
        timestamp = datetime.now().strftime("[%H:%M:%S]")
        return f"{timestamp} {message}\n"

    def _is_near_bottom(self, widget, margin=0.02):
        """
        True als de zichtbare view praktisch onderaan zit.
        margin=0.02 betekent: binnen de onderste 2% tellen we als 'onderaan'.
        """
        try:
            first, last = widget.yview()  # last=1.0 is exact bottom
            return last >= (1.0 - margin)
        except Exception:
            return True  # fail-safe: treat as bottom to avoid breaking logging

    def _go_top(self, widget):
        """Scroll naar boven en zet tail-follow uit voor deze widget."""
        if not widget:
            return
        try:
            widget.see("1.0")
        except Exception:
            pass
        try:
            self._log_follow_tail[widget] = False
        except Exception:
            pass

    def _go_bottom(self, widget):
        """Scroll naar beneden en zet tail-follow aan voor deze widget."""
        if not widget:
            return
        try:
            widget.see(tk.END)
        except Exception:
            pass
        try:
            self._log_follow_tail[widget] = True
        except Exception:
            pass

    def _toggle_auto_follow(self):
        """
        Wordt aangeroepen door de checkbox.
        - Aan: zet follow aan en springt naar bottom (voor beide logs).
        - Uit: zet follow uit (voor beide logs).
        """
        enabled = bool(self.auto_follow_var.get())

        for w in (self.log_text, self.log_text_extended):
            if not w:
                continue
            try:
                self._log_follow_tail[w] = enabled
            except Exception:
                pass

            # Als we aanzetten, meteen naar beneden zodat je live kan meekijken
            if enabled:
                try:
                    w.see(tk.END)
                except Exception:
                    pass

    def _register_log_widget(self, widget):
        """Initialiseer tail-follow state voor nieuwe log Text widgets."""
        try:
            self._log_follow_tail[widget] = True  # start: follow tail
        except Exception:
            pass

    def _scroll_start(self, widget):
        """Markeer dat user actief scrollt; voorkom autoscroll-jumps tijdens logging."""
        try:
            self._log_user_scrolling.add(widget)
            after_id = self._log_scroll_after_ids.pop(widget, None)
            if after_id:
                self.master.after_cancel(after_id)
        except Exception:
            pass

    def _scroll_end(self, widget, snap_if_bottom=True):
        """
        User stopt met scrollen (mouse release / wheel idle).
        We bepalen hier 'netjes' of tail-follow weer aan mag.
        """
        try:
            if widget in self._log_user_scrolling:
                self._log_user_scrolling.remove(widget)

            follow = self._is_near_bottom(widget)
            self._log_follow_tail[widget] = follow

            if snap_if_bottom and follow:
                widget.see(tk.END)
        except Exception:
            pass

    def _schedule_scroll_end(self, widget, delay_ms=350):
        """
        Voor muiswiel: pas na korte idle tijd scroll_end uitvoeren.
        (Zodat hij tijdens wheelen niet ineens naar end gaat.)
        """
        try:
            # reset timer
            after_id = self._log_scroll_after_ids.pop(widget, None)
            if after_id:
                self.master.after_cancel(after_id)

            self._log_scroll_after_ids[widget] = self.master.after(
                delay_ms, lambda w=widget: self._scroll_end(w, snap_if_bottom=True)
            )
        except Exception:
            pass

    def _append_to_log_widget(self, widget, formatted_message, tag, add_newline=False):
        """
        Appends a formatted message to a Tkinter Text widget.
        """
        if not widget:
            return

        if add_newline:
            widget.insert(tk.END, "\n")

        widget.insert(tk.END, formatted_message, tag)

        # Autoscroll alleen als:
        # - Auto-follow aan staat
        # - gebruiker niet actief aan het scrollen is
        # - én tail-follow True is voor deze widget
        try:
            if self.auto_follow_var.get():
                if widget not in self._log_user_scrolling:
                    follow = self._log_follow_tail.get(widget, True)
                    if follow:
                        widget.see(tk.END)
        except Exception:
            pass

        try:
            widget.update_idletasks()
        except Exception:
            pass

    def _write_log_file(self, file_path, formatted_message, add_newline=False, warning_prefix="Warning"):
        """
        Writes a formatted log message to a file.
        """
        try:
            with open(file_path, "a", encoding="utf-8") as f:
                if add_newline:
                    f.write("\n")
                f.write(formatted_message)
        except Exception as e:
            print(f"{warning_prefix}: Could not write to log file: {e}")


    def _emit_extended_log(self, formatted_message, tag, add_newline=False):
        """
        Writes to the extended GUI log and extended logfile.
        """
        self._append_to_log_widget(self.log_text_extended, formatted_message, tag, add_newline)

        if self.save_ext_log_var.get():
            self._write_log_file(
                self.log_file_extended_path,
                formatted_message,
                add_newline=add_newline,
                warning_prefix="Warning"
            )


    def _emit_standard_log(self, formatted_message, tag, add_newline=False):
        """
        Writes to the standard GUI log and standard logfile.
        Falls back to console if the standard GUI log widget does not exist.
        """
        if self.log_text:
            self._append_to_log_widget(self.log_text, formatted_message, tag, add_newline)
        else:
            if add_newline:
                print("")
            print(formatted_message.strip())

        if self.save_std_log_var.get():
            self._write_log_file(
                self.log_file_path,
                formatted_message,
                add_newline=add_newline,
                warning_prefix="Warning"
            )


    def _log_message_ui(self, message, message_type='info', extended_only=False):
        """
        Performs the actual log write on the Tkinter main thread.
        Uses structured helper methods for normalization, formatting, tagging,
        widget output, and file output.
        """
        clean_message, add_newline = self._normalize_log_message(message)
        tag = self._determine_log_tag(clean_message, message_type)
        formatted_message = self._format_log_message(clean_message)

        # Extended log always gets the full message
        self._emit_extended_log(formatted_message, tag, add_newline)

        # Standard log only if not explicitly extended-only
        if not extended_only:
            self._emit_standard_log(formatted_message, tag, add_newline)


    def log_message(self, message, message_type='info', extended_only=False):
        """
        Thread-safe logging entry point.
        If called from the main thread, log directly.
        If called from a worker thread, queue the log event for UI processing.
        """
        if threading.current_thread() is threading.main_thread():
            self._log_message_ui(message, message_type, extended_only)
        else:
            self.ui_queue.put(("log", message, message_type, extended_only))
    
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
        """Updates the Max Mapillary action controls based on the selected main workflow."""
        choice = self.workflow_choice.get()
        enable_mapillary = (choice in [1, 3])

        mapillary_state = tk.NORMAL if enable_mapillary else tk.DISABLED
        label_fg = '#000000' if enable_mapillary else '#888888'

        if hasattr(self, 'rb_max_process_upload'):
            self.rb_max_process_upload.config(state=mapillary_state)

        if hasattr(self, 'rb_max_process_only'):
            self.rb_max_process_only.config(state=mapillary_state)

        if hasattr(self, 'rb_max_upload_only'):
            self.rb_max_upload_only.config(state=mapillary_state)

        if hasattr(self, 'lbl_max_mapillary_actions'):
            self.lbl_max_mapillary_actions.config(fg=label_fg)
    
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

    # --- Configuration Functions ---
    def load_settings(self):
        """Loads settings from the JSON file and updates UI variables."""
        if os.path.exists(self.config_file): 
            try:
                with open(self.config_file, 'r') as f:
                    loaded_settings = json.load(f)
                
                # Update UI Variables
                self.source_dir_var.set(loaded_settings.get('SourceDir', ""))
                self.target_dir_var.set(loaded_settings.get('TargetDir', ""))
                self.hero_source_dir_var.set(loaded_settings.get('HeroSourceDir', ""))
                self.hero_target_dir_var.set(loaded_settings.get('HeroTargetDir', ""))
                
                if not getattr(sys, 'frozen', False):
                    self.utility_path_var.set(loaded_settings.get('UtilityPath', ""))
                
                self.imagemagick_path_var.set(loaded_settings.get('ImageMagickPath', ""))
                self.nadir_image_path_var.set(loaded_settings.get('NadirImagePath', ""))
                self.nadir_scale_var.set(str(loaded_settings.get('NadirScaleFactor', 0.2500)))
                self.nadir_crf_var.set(str(loaded_settings.get('NadirCRF', 17)))
                self.nadir_qp_var.set(str(loaded_settings.get('NadirQP', 18)))
                self.cineform_crf_var.set(int(loaded_settings.get('CineformCRF', 15)))
                self.cineform_qp_var.set(int(loaded_settings.get('CineformQP', 16)))
                self.parallel_nadir_jobs_var.set(int(loaded_settings.get('ParallelNadirJobs', 1)))

                self.mapillary_user_var.set(loaded_settings.get('MapillaryUserName', ""))
                self.sample_distance_var.set(str(loaded_settings.get('VideoSampleDistance', 3.0)))
                self.upload_workers_var.set(str(loaded_settings.get('MapillaryUploadWorkers', 8)))
                
                self.file_suffix_var.set(loaded_settings.get('FileSuffix', ""))
                self.use_gpu_encoding_var.set(loaded_settings.get('UseGPUEncoding', False))
                self.gpu_encoder_var.set(loaded_settings.get('GPUEncoder', 'auto'))
                
                # Load Logging Preferences
                self.save_std_log_var.set(loaded_settings.get('SaveStandardLog', True))
                self.save_ext_log_var.set(loaded_settings.get('SaveExtendedLog', True))
                
                self.update_settings_dict()
                return True
                
            except Exception as e:
                print(f"[ERROR] Error loading settings: {e}")
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
            'NadirQP': self.settings['NadirQP'],
            'CineformCRF': self.settings['CineformCRF'],
            'CineformQP': self.settings['CineformQP'],
            'SaveStandardLog': self.settings['SaveStandardLog'],
            'SaveExtendedLog': self.settings['SaveExtendedLog'],
            'ParallelNadirJobs': self.settings['ParallelNadirJobs'],
            'FFmpegPriority': self.settings.get('FFmpegPriority', 'belownormal')
        }

        import time
        max_retries = 3
        for i in range(max_retries):
            try:
                with open(self.config_file, 'w') as f: 
                    json.dump(settings_to_save, f, indent=4)
                self.log_message(f"[SUCCESS] Settings saved to '{self.config_file}'.", 'success')
                messagebox.showinfo("Settings Saved", "Configuration has been saved successfully.")
                break 
            except PermissionError:
                if i < max_retries - 1:
                    time.sleep(0.5)
                    continue
                else:
                    raise 
            except Exception as e:
                self.log_message(f"[ERROR] Failed to save settings: {e}", 'error')
                messagebox.showerror("Error", f"Could not save settings: {e}")
                break

    def update_settings_dict(self):
        """Updates the internal settings dictionary."""
        self.settings['SourceDir'] = self.source_dir_var.get()
        self.settings['TargetDir'] = self.target_dir_var.get()
        self.settings['HeroSourceDir'] = self.hero_source_dir_var.get()
        self.settings['HeroTargetDir'] = self.hero_target_dir_var.get()
        self.settings['MapillaryUserName'] = self.mapillary_user_var.get()
        self.settings['SaveStandardLog'] = self.save_std_log_var.get()
        self.settings['SaveExtendedLog'] = self.save_ext_log_var.get()
        try:
            self.settings['MapillaryUploadWorkers'] = self.upload_workers_var.get()
            if self.settings['MapillaryUploadWorkers'] < 1:
                self.settings['MapillaryUploadWorkers'] = 1
        except (tk.TclError, ValueError, TypeError):
            self.settings['MapillaryUploadWorkers'] = 8

        self.settings['NadirImagePath'] = self.nadir_image_path_var.get()

        try:
            self.settings['NadirScaleFactor'] = self.nadir_scale_var.get()
        except (tk.TclError, ValueError, TypeError):
            self.settings['NadirScaleFactor'] = 0.2500

        try:
            self.settings['NadirCRF'] = self.nadir_crf_var.get()
        except (tk.TclError, ValueError, TypeError):
            self.settings['NadirCRF'] = 17

        try:
            self.settings['NadirQP'] = self.nadir_qp_var.get()
        except (tk.TclError, ValueError, TypeError):
            self.settings['NadirQP'] = 18

        try:
            v = int(self.parallel_nadir_jobs_var.get())
            if v < 1:
                v = 1
            if v > 4:
                v = 4
            self.settings['ParallelNadirJobs'] = v
        except (tk.TclError, ValueError, TypeError):
            self.settings['ParallelNadirJobs'] = 1

        if 'FFmpegPriority' not in self.settings:
            self.settings['FFmpegPriority'] = 'belownormal'

        try:
            self.settings['CineformCRF'] = self.cineform_crf_var.get()
        except (tk.TclError, ValueError, TypeError):
            self.settings['CineformCRF'] = 15

        try:
            self.settings['CineformQP'] = self.cineform_qp_var.get()
        except (tk.TclError, ValueError, TypeError):
            self.settings['CineformQP'] = 16

        try:
            self.settings['VideoSampleDistance'] = self.sample_distance_var.get()
        except (tk.TclError, ValueError, TypeError):
            self.settings['VideoSampleDistance'] = 3.0
            
        suffix_input = self.file_suffix_var.get().strip()
        if not suffix_input:
            self.settings['FileSuffix'] = ""
        else:
            self.settings['FileSuffix'] = re.sub(r'^\s*_*|\s*', '', suffix_input)
            
        self.settings['CameraModel'] = 'AUTO'
        self.settings['UseGPUEncoding'] = self.use_gpu_encoding_var.get()
        self.settings['GPUEncoder'] = self.gpu_encoder_var.get()

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

    def browse_directory(self, var, *args):
        """Opens a directory selection dialog."""
        directory = filedialog.askdirectory()
        if directory:
            var.set(directory)

    def browse_file(self, var, *args):
        """Opens a file selection dialog. *args catches the optional filetypes filter."""
        # If the first item in args is a list/tuple, use it as filetypes
        filetypes = args[0] if args and isinstance(args[0], (list, tuple)) else [("All Files", "*.*")]
        
        filename = filedialog.askopenfilename(filetypes=filetypes)
        if filename:
            var.set(filename)
            
    def create_config_tab(self, tab):
        tab.grid_rowconfigure(0, weight=1)
        tab.grid_columnconfigure(0, weight=1)
        
        is_frozen = getattr(sys, 'frozen', False)
        is_path_browsable = not is_frozen
        
        canvas = tk.Canvas(tab, bg=self.system_bg_color, highlightthickness=0, bd=0)
        scrollable_frame = tk.Frame(canvas, bg=self.system_bg_color)
        scrollable_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        scrollable_frame.grid_columnconfigure(0, weight=1)
        canvas_window = canvas.create_window((0, 0), window=scrollable_frame, anchor="nw") 
        
        def on_canvas_resize(event):
            canvas.itemconfig(canvas_window, width=event.width)
        canvas.bind('<Configure>', on_canvas_resize)
        canvas.grid(row=0, column=0, sticky='nsew')
        content_frame = scrollable_frame
        
        # --- LOGO (100x100, centered) ---
        if self.logo_image:
            try:
                pil_image_new = Image.open(resource_path("Banner_side.png"))
                pil_image_new.thumbnail((302, 100)) 
                self.logo_image_small = ImageTk.PhotoImage(pil_image_new)
                tk.Label(content_frame, image=self.logo_image_small, bg=self.system_bg_color).pack(pady=10)
            except Exception as e:
                print(f"Error loading logo: {e}")

        # =========================================================================
        # 1. GOPRO LOCATIONS (MAX & HERO COMBINED)
        # =========================================================================
        dir_group_frame = ttk.LabelFrame(content_frame, text="GoPro Locations (Max & Hero)", padding="10")
        dir_group_frame.pack(padx=20, pady=5, fill='x', expand=True)
        
        dir_input_frame = ttk.Frame(dir_group_frame)
        dir_input_frame.pack(padx=10, pady=5, fill='x', expand=True)
        dir_input_frame.grid_columnconfigure(1, weight=1)

        self._create_input_field_grid(dir_input_frame, "Max Source Location:", self.source_dir_var, row=0, col=0, colspan=2)
        self._create_input_field_grid(dir_input_frame, "Max Target Location:", self.target_dir_var, row=1, col=0, colspan=2)
        self._create_input_field_grid(dir_input_frame, "Hero Source Location:", self.hero_source_dir_var, row=2, col=0, colspan=2)
        self._create_input_field_grid(dir_input_frame, "Hero Target Location:", self.hero_target_dir_var, row=3, col=0, colspan=2)

        # =========================================================================
        # 2. GENERAL SETTINGS & TOOLS
        # =========================================================================
        gen_group_frame = ttk.LabelFrame(content_frame, text="General Settings & Tools", padding="10")
        gen_group_frame.pack(padx=20, pady=5, fill='x', expand=True)
        
        gen_frame = ttk.Frame(gen_group_frame)
        gen_frame.pack(padx=10, pady=5, fill='x', expand=True)
        
        # 5 Columns for perfect alignment
        gen_frame.grid_columnconfigure(1, weight=1) 
        gen_frame.grid_columnconfigure(3, weight=1) 
        gen_frame.grid_columnconfigure(4, weight=0) 
        
        # ROW 0: Utility Location
        tk.Label(gen_frame, text="Utility Location:", bg=self.system_bg_color).grid(row=0, column=0, sticky='w', padx=5, pady=5)
        util_entry = ttk.Entry(gen_frame, textvariable=self.utility_path_var)
        util_entry.grid(row=0, column=1, columnspan=3, sticky='ew', padx=5, pady=5)
        
        # Button disappears only in EXE
        if is_path_browsable:
            ttk.Button(gen_frame, text="Browse Dir...", command=lambda: self.browse_directory(self.utility_path_var)).grid(row=0, column=4, sticky='w', padx=5, pady=5)
        else:
            util_entry.config(state='disabled')

        tk.Label(gen_frame, text="Mapillary Profile Name:", bg=self.system_bg_color).grid(
            row=1, column=0, sticky='w', padx=5, pady=5
        )
        profile_entry = ttk.Entry(gen_frame, textvariable=self.mapillary_user_var)
        profile_entry.grid(row=1, column=1, sticky='ew', padx=5, pady=5)

        tk.Label(gen_frame, text="File Suffix (Optional):", bg=self.system_bg_color).grid(
            row=1, column=2, sticky='w', padx=15, pady=5
        )
        suffix_entry = ttk.Entry(gen_frame, textvariable=self.file_suffix_var)
        suffix_entry.grid(row=1, column=3, sticky='ew', padx=5, pady=5)

        tk.Label(gen_frame, text="Sample Distance (m):", bg=self.system_bg_color).grid(
            row=2, column=0, sticky='w', padx=5, pady=5
        )
        sample_entry = ttk.Entry(gen_frame, textvariable=self.sample_distance_var)
        sample_entry.grid(row=2, column=1, sticky='ew', padx=5, pady=5)

        tk.Label(gen_frame, text="Upload Workers:", bg=self.system_bg_color).grid(
            row=2, column=2, sticky='w', padx=15, pady=5
        )
        workers_entry = ttk.Entry(gen_frame, textvariable=self.upload_workers_var)
        workers_entry.grid(row=2, column=3, sticky='ew', padx=5, pady=5)

        create_tooltip(
            profile_entry,
            "This is the Mapillary profile name used by Mapillary Tools during upload.\n"
            "It must match the configured local profile used for upload.\n"
            "If upload fails, first create or activate your account via www.mapillary.com."
        )

        create_tooltip(
            suffix_entry,
            "Optional suffix added to output names.\n"
            "Example: 04042026 or ProjectA\n"
            "Leave empty if no suffix is needed."
        )

        create_tooltip(
            sample_entry,
            "Distance in meters between extracted frames.\n"
            "Lower value = more images\n"
            "Higher value = fewer images\n"
            "Typical value: 3.0"
        )

        create_tooltip(
            workers_entry,
            "Number of parallel upload workers used by Mapillary Tools.\n"
            "Minimum = 1\n"
            "Higher values may improve upload speed depending on system/network."
        )

        # ROW 3: Save Standard Log + Save Extended Log (same row)
        tk.Label(gen_frame, text="Save Standard Log (.txt):", anchor='w', bg=self.system_bg_color).grid(
            row=3, column=0, sticky='w', padx=5, pady=5
        )
        ttk.Checkbutton(gen_frame, variable=self.save_std_log_var).grid(
            row=3, column=1, sticky='w', padx=5, pady=5
        )

        tk.Label(gen_frame, text="Save Extended Log (.txt):", anchor='w', bg=self.system_bg_color).grid(
            row=3, column=2, sticky='w', padx=15, pady=5
        )
        ttk.Checkbutton(gen_frame, variable=self.save_ext_log_var).grid(
            row=3, column=3, sticky='w', padx=5, pady=5
        )
        
        # ROW 4: CineForm Quality Settings
        tk.Label(gen_frame, text="CineForm HEVC CRF:", bg=self.system_bg_color).grid(
            row=4, column=0, sticky='w', padx=5, pady=5
        )
        cine_crf_spin = ttk.Spinbox(
            gen_frame, from_=0, to=51, textvariable=self.cineform_crf_var, width=5,
            command=self.update_settings_dict
        )
        cine_crf_spin.grid(row=4, column=1, sticky='w', padx=5, pady=5)

        cine_crf_spin.bind('<Return>', lambda e: self.update_settings_dict())
        cine_crf_spin.bind('<FocusOut>', lambda e: self.update_settings_dict())

        tk.Label(gen_frame, text="CineForm HEVC QP:", bg=self.system_bg_color).grid(
            row=4, column=2, sticky='w', padx=15, pady=5
        )
        cine_qp_spin = ttk.Spinbox(
            gen_frame, from_=0, to=51, textvariable=self.cineform_qp_var, width=5,
            command=self.update_settings_dict
        )
        cine_qp_spin.grid(row=4, column=3, sticky='w', padx=5, pady=5)
        cine_qp_spin.bind('<Return>', lambda e: self.update_settings_dict())

        cine_qp_spin.bind('<FocusOut>', lambda e: self.update_settings_dict())
        
        create_tooltip(
            cine_crf_spin,
            "CRF used when the detected source codec is CineForm and the output is encoded to HEVC.\n"
            "Limits: 0-51 (0 is lossless, 51 is worst).\n"
            "Lower value = better quality / larger file.\n"
            "Recommended high-quality default: 15."
        )

        create_tooltip(
            cine_qp_spin,
            "QP used for GPU-based HEVC encoding when the detected source codec is CineForm.\n"
            "Lower value = better quality / larger file.\n"
            "Recommended high-quality default: 16."
        )

        # =========================================================================
        # 3. NADIR SETTINGS (MAX ONLY)
        # =========================================================================
        nadir_group_frame = ttk.LabelFrame(content_frame, text="Nadir Settings (Max Only)", padding="10")
        nadir_group_frame.pack(padx=20, pady=5, fill='x', expand=True)
        
        nadir_frame = ttk.Frame(nadir_group_frame)
        nadir_frame.pack(padx=10, pady=5, fill='x', expand=True)
        nadir_frame.grid_columnconfigure(1, weight=1); nadir_frame.grid_columnconfigure(3, weight=1); nadir_frame.grid_columnconfigure(4, weight=0)

        # ROW 0: ImageMagick Location - Always show browse button
        tk.Label(nadir_frame, text="ImageMagick Location:", bg=self.system_bg_color).grid(row=0, column=0, sticky='w', padx=5, pady=5)
        magick_entry = ttk.Entry(nadir_frame, textvariable=self.imagemagick_path_var)
        magick_entry.grid(row=0, column=1, columnspan=3, sticky='ew', padx=5, pady=5)
        ttk.Button(nadir_frame, text="Browse File...", 
                   command=lambda: self.browse_file(self.imagemagick_path_var, [("Executables", "*.exe")])).grid(row=0, column=4, sticky='w', padx=5, pady=5)

        # ROW 1: Nadir Image (PNG) - Always show browse button
        tk.Label(nadir_frame, text="Nadir Image (PNG):", bg=self.system_bg_color).grid(row=1, column=0, sticky='w', padx=5, pady=5)
        nadir_img_entry = ttk.Entry(nadir_frame, textvariable=self.nadir_image_path_var)
        nadir_img_entry.grid(row=1, column=1, columnspan=3, sticky='ew', padx=5, pady=5)
        ttk.Button(nadir_frame, text="Browse File...", 
                   command=lambda: self.browse_file(self.nadir_image_path_var, [("Images", "*.png")])).grid(row=1, column=4, sticky='w', padx=5, pady=5)

        # ROW 2: Scale Factor & CRF 
        tk.Label(nadir_frame, text="Scale Factor:", bg=self.system_bg_color).grid(row=2, column=0, sticky='w', padx=5, pady=5)
        ttk.Entry(nadir_frame, textvariable=self.nadir_scale_var).grid(row=2, column=1, sticky='ew', padx=5, pady=5)

        tk.Label(nadir_frame, text="Video Quality (CRF):", bg=self.system_bg_color).grid(
            row=2, column=2, sticky='w', padx=15, pady=5
        )

        crf_spin = ttk.Spinbox(
            nadir_frame, from_=0, to=51, textvariable=self.nadir_crf_var, width=5,
            command=self.update_settings_dict
        )
        crf_spin.grid(row=2, column=3, sticky='w', padx=5, pady=5)

        crf_spin.bind('<Return>', lambda e: self.update_settings_dict())
        crf_spin.bind('<FocusOut>', lambda e: self.update_settings_dict())
        
        create_tooltip(
            crf_spin,
            "Constant Rate Factor (CPU).\n"
            "Limits: 0-51 (0 is lossless, 51 is worst).\n"
            "Lower value = Better Quality (Larger Files).\n"
            "Higher value = Lower Quality (Smaller Files).\n"
            "Default: 17-24 is good quality."
        )
        
        # Nadir jobs (same row as CRF)
        tk.Label(
            nadir_frame,
            text="Nadir jobs:",
            bg=self.system_bg_color
        ).grid(row=2, column=4, sticky='w', padx=20, pady=5)

        nadir_jobs_spin = ttk.Spinbox(
            nadir_frame,
            from_=1, to=4,
            textvariable=self.parallel_nadir_jobs_var,
            width=4,
            command=self.update_settings_dict
        )
        nadir_jobs_spin.grid(row=2, column=5, sticky='w', padx=5, pady=5)
        
        nadir_jobs_spin.bind('<Return>', lambda e: self.update_settings_dict())
        nadir_jobs_spin.bind('<FocusOut>', lambda e: self.update_settings_dict())

        create_tooltip(
            nadir_jobs_spin,
            "Parallel Nadir encodes.\n"
            "1 = Safe for older systems.\n"
            "2 = Recommended for modern systems.\n"
            "Warning: more jobs = higher CPU/GPU load!"
)

        # =========================================================================
        # 4. GPU SETTINGS
        # =========================================================================
        gpu_group_frame = ttk.LabelFrame(content_frame, text="GPU Acceleration (Nadir & Max Encoding)", padding="10")
        gpu_group_frame.pack(padx=20, pady=5, fill='x', expand=True)
        
        gpu_frame = ttk.Frame(gpu_group_frame)
        gpu_frame.pack(padx=10, pady=5, fill='x', expand=True)
        gpu_frame.grid_columnconfigure(1, weight=1); gpu_frame.grid_columnconfigure(3, weight=1)

        # 1. Enable GPU
        if not hasattr(self, 'use_gpu_encoding_var'):
             self.use_gpu_encoding_var = tk.BooleanVar(value=self.settings.get('UseGPUEncoding', False))

        ttk.Checkbutton(gpu_frame, text="Enable GPU Encoding", variable=self.use_gpu_encoding_var, 
                        onvalue=True, offvalue=False, command=self.update_settings_dict).grid(row=0, column=0, columnspan=4, sticky='w', pady=(0, 10))
        
        # 2. Preferred Encoder
        tk.Label(gpu_frame, text="Preferred Encoder:", anchor='w', bg=self.system_bg_color).grid(row=1, column=0, sticky='w', padx=5, pady=5)
        
        encoders = ['auto (Recommended)', 'nvenc (NVIDIA)', 'qsv (Intel Quick Sync)', 'amf (AMD)']
        if not hasattr(self, 'gpu_encoder_var'):
             self.gpu_encoder_var = tk.StringVar(value=self.settings.get('GPUEncoder', 'auto'))
        
        gpu_encoder_combo = ttk.Combobox(gpu_frame, textvariable=self.gpu_encoder_var, values=encoders, state="readonly", width=22)
        gpu_encoder_combo.grid(row=1, column=1, sticky='w', padx=5, pady=5)
        gpu_encoder_combo.bind("<<ComboboxSelected>>", lambda e: self.update_settings_dict())

        # 3. GPU Quality QP
        tk.Label(gpu_frame, text="GPU Quality (QP 0-51):", anchor='w', bg=self.system_bg_color).grid(row=1, column=2, sticky='w', padx=15, pady=5)
        
        if not hasattr(self, 'nadir_qp_var'):
            self.nadir_qp_var = tk.IntVar(value=self.settings.get('NadirQP', 18))
            
        qp_spin = ttk.Spinbox(gpu_frame, from_=0, to=51, textvariable=self.nadir_qp_var, width=5, command=self.update_settings_dict)
        qp_spin.grid(row=1, column=3, sticky='w', padx=5, pady=5)
        
        qp_spin.bind('<Return>', lambda e: self.update_settings_dict())
        qp_spin.bind('<FocusOut>', lambda e: self.update_settings_dict())
        
        try:
            qp_tooltip_text = (
                "GPU Quantization Parameter (QP).\n"
                "Limits: 0-51 (0 is best, 51 is worst).\n"
                "Lower value = Better Quality (Larger Files).\n"
                "Higher value = Lower Quality (Smaller Files).\n"
                "A value of ~24 is roughly equivalent to CPU CRF 17."
            )
            create_tooltip(qp_spin, qp_tooltip_text)
        except Exception as e:
            print(f"Warning: Could not create GPU QP tooltip: {e}")
        
        # --- SAVE & RELOAD BUTTONS ---
        button_frame = ttk.Frame(content_frame)
        button_frame.pack(pady=20)
        ttk.Button(button_frame, text="Save Settings", command=self.save_settings, style='TButton').pack(side='left', padx=10)
        ttk.Button(button_frame, text="Reload Settings", command=self.load_settings, style='TButton').pack(side='left', padx=10)
        # Check Config button removed - 5.2.0
        
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
        entry.config(style='TEntry')
        entry.grid(row=0, column=1, padx=0, sticky='ew')
        
        if key: self.dir_entries[key] = entry 
        
        if tooltip:
            create_tooltip(label, tooltip)
            create_tooltip(entry, tooltip)
            if button: create_tooltip(button, tooltip)
    
    def create_max_workflow_tab(self, tab):
        tab.grid_rowconfigure(0, weight=1)
        tab.grid_columnconfigure(0, weight=1)
        
        canvas = tk.Canvas(tab, bg=self.system_bg_color, highlightthickness=0, bd=0)
        canvas.grid(row=0, column=0, sticky='nsew')
        
        scrollable_frame = tk.Frame(canvas, bg=self.system_bg_color)
        
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
                 text="Before executing any steps within this tool, you must first convert your original .360 files "
                      "using the GoPro Player Batch Exporter. \n"
                      "Please use the following settings in the GoPro Player Batch Exporter:\n\n"
                      "  * Codec: HEVC or CineForm (best quality, x10 file size!)\n"
                      "  * Resolution: Select the resolution corresponding to your source file settings.\n"
                      "  * Bitrate: Maximum/High (CineForm)\n"
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
        
        # --- ROW 0: Camera Family Detection ---
        tk.Label(
            selection_container,
            text="Camera Family Detection",
            font=('Arial', 10, 'bold'),
            bg=self.system_bg_color
        ).grid(row=0, column=0, columnspan=3, sticky='w', pady=(0, 5))

        tk.Label(
            selection_container,
            text="Automatic from .360 metadata (Max 1 / Max 2 / mixed source sets supported)",
            bg=self.system_bg_color,
            fg='#006400'
        ).grid(row=1, column=0, columnspan=3, sticky='w', padx=5)
        
        # --- ROW 2: Main Workflow ---
        tk.Label(selection_container, text="Choose Main Workflow", font=('Arial', 10, 'bold'), bg=self.system_bg_color).grid(row=2, column=0, columnspan=3, sticky='w', pady=(15, 5))
        
        ttk.Radiobutton(selection_container, text="1) Mapillary processing", variable=self.workflow_choice, value=1, command=self.update_workflow_options).grid(row=3, column=0, sticky='w', padx=5)
        ttk.Radiobutton(selection_container, text="2) Streetview Studio processing", variable=self.workflow_choice, value=2, command=self.update_workflow_options).grid(row=3, column=1, sticky='w', padx=5)
        ttk.Radiobutton(selection_container, text="3) Run all", variable=self.workflow_choice, value=3, command=self.update_workflow_options).grid(row=3, column=2, sticky='w', padx=5)

        # --- ROW 4: Mapillary Actions (Max Tab) ---
        self.lbl_max_mapillary_actions = tk.Label(
            selection_container,
            text="Mapillary Actions Options",
            font=('Arial', 10, 'bold'),
            bg=self.system_bg_color,
            fg='#000000'
        )
        self.lbl_max_mapillary_actions.grid(row=4, column=0, columnspan=3, sticky='w', pady=(15, 5))
        
        # Option 1: Process & Upload
        self.rb_max_process_upload = ttk.Radiobutton(
            selection_container,
            text="Sample, Process and Upload",
            variable=self.mapillary_actions_var,
            value=1
        )
        self.rb_max_process_upload.grid(row=5, column=0, sticky='w', padx=5)
        
        # Option 2: Process Only
        self.rb_max_process_only = ttk.Radiobutton(
            selection_container,
            text="Sample & Process Only (No Upload)",
            variable=self.mapillary_actions_var,
            value=2
        )
        self.rb_max_process_only.grid(row=5, column=1, sticky='w', padx=5)

        # Option 3: Upload Only
        self.rb_max_upload_only = ttk.Radiobutton(
            selection_container,
            text="Upload Only",
            variable=self.mapillary_actions_var,
            value=3
        )
        self.rb_max_upload_only.grid(row=5, column=2, sticky='w', padx=5)

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
        
        canvas = tk.Canvas(tab, bg=self.system_bg_color, highlightthickness=0, bd=0)
        canvas.grid(row=0, column=0, sticky='nsew')
        scrollable_frame = tk.Frame(canvas, bg=self.system_bg_color)
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
        
        # Option 1
        ttk.Radiobutton(selection_container, text="Sample, Process and Upload", variable=self.hero_mapillary_actions_var, value=1).pack(anchor='w', pady=5)
        # Option 2
        ttk.Radiobutton(selection_container, text="Sample and Process Only (No Upload)", variable=self.hero_mapillary_actions_var, value=2).pack(anchor='w', pady=5)
        # Option 3
        ttk.Radiobutton(selection_container, text="Upload Only", variable=self.hero_mapillary_actions_var, value=3).pack(anchor='w', pady=5)
        
        button_container = ttk.Frame(content_frame, padding="20 0 20 0") 
        button_container.pack(pady=20, fill='x') 
        ttk.Button(button_container, text="START HERO WORKFLOW", command=self.start_hero_workflow, style='Accent.Big.TButton').pack(pady=0, fill='x')
    
    # --- LOG TABS ---
    def create_log_tab_content(self, tab):
        """Creates the log text widget, scrollbar, and controls inside the main log tab."""
        tab.grid_rowconfigure(1, weight=1) 
        tab.grid_columnconfigure(0, weight=1)
        
        # 1. Title + Bottom button (header row)
        header = tk.Frame(tab, bg=self.system_bg_color)
        header.grid(row=0, column=0, sticky='ew', padx=10, pady=10)
        header.grid_columnconfigure(0, weight=1)

        tk.Label(
            header,
            text="WORKFLOW - OUTPUT AND LOGS",
            font=('Arial', 12, 'bold'),
            bg=self.system_bg_color
        ).grid(row=0, column=0, sticky='w')
            
        ttk.Button(
            header,
            text="Top",
            width=8,
            command=lambda: self._go_top(self.log_text)
        ).grid(row=0, column=1, sticky='e', padx=(0, 6))

        ttk.Button(
            header,
            text="Bottom",
            width=10,
            command=lambda: self._go_bottom(self.log_text)
        ).grid(row=0, column=2, sticky='e')
        
        ttk.Checkbutton(
            header,
            text="Auto-follow",
            variable=self.auto_follow_var,
            command=self._toggle_auto_follow
        ).grid(row=0, column=3, sticky='e', padx=(12, 0))

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
        self._register_log_widget(self.log_text)
        # Mousewheel: lock tijdens wheelen + unlock na korte idle (netter)
        self.log_text.bind(
            "<MouseWheel>",
            lambda e, w=self.log_text: (self._scroll_start(w), self._schedule_scroll_end(w, delay_ms=350))
        )
        self.log_text.bind("<ButtonPress-1>",  lambda e, w=self.log_text: self._scroll_start(w))
        self.log_text.bind("<ButtonRelease-1>", lambda e, w=self.log_text: self._scroll_end(w, snap_if_bottom=True))
        # Go to bottom shortcut (Windows): Ctrl+End
        self.log_text.bind("<Control-End>", lambda e: (self.log_text.see(tk.END), "break"))
        self.log_text.bind("<Control-Home>", lambda e: (self.log_text.see("1.0"), "break"))  # optioneel: naar boven

        scrollbar.config(command=self.log_text.yview)
        scrollbar.bind("<ButtonPress-1>",  lambda e, w=self.log_text: self._scroll_start(w))
        scrollbar.bind("<B1-Motion>",      lambda e, w=self.log_text: self._scroll_start(w))
        scrollbar.bind("<ButtonRelease-1>", lambda e, w=self.log_text: self._scroll_end(w, snap_if_bottom=True))

        # Tags
        self.log_text.tag_config('error', foreground='red')
        self.log_text.tag_config('success', foreground='green')
        self.log_text.tag_config('warning', foreground='#FF8C00') # Orange-ish
        # Nadir process color tags (P1..P4)
        self.log_text.tag_config('nadir_p1', foreground='#ff4fa3')  # pink
        self.log_text.tag_config('nadir_p2', foreground='#7b61ff')  # purple
        self.log_text.tag_config('nadir_p3', foreground='#00a6a6')  # teal
        self.log_text.tag_config('nadir_p4', foreground='#b06c2f')  # bronze
        
        # 3. Progress & Stop Button Frame
        button_frame = ttk.Frame(tab, padding="5 0 5 0") 
        button_frame.grid(row=2, column=0, sticky='ew', padx=10, pady=(0, 10))
        
        self.progress_bar = ttk.Progressbar(button_frame, orient="horizontal", mode="determinate", style="Main.Horizontal.TProgressbar")
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

        # 1. Title + Bottom button (header row)
        header = tk.Frame(tab, bg=self.system_bg_color)
        header.grid(row=0, column=0, sticky='ew', padx=10, pady=10)
        header.grid_columnconfigure(0, weight=1)

        tk.Label(
            header,
            text="WORKFLOW - EXTENDED OUTPUT AND LOGS",
            font=('Arial', 12, 'bold'),
            bg=self.system_bg_color
        ).grid(row=0, column=0, sticky='w')    
       
        ttk.Button(
            header,
            text="Top",
            width=8,
            command=lambda: self._go_top(self.log_text_extended)
        ).grid(row=0, column=1, sticky='e', padx=(0, 6))

        ttk.Button(
            header,
            text="Bottom",
            width=10,
            command=lambda: self._go_bottom(self.log_text_extended)
        ).grid(row=0, column=2, sticky='e')
        
        ttk.Checkbutton(
            header,
            text="Auto-follow",
            variable=self.auto_follow_var,
            command=self._toggle_auto_follow
        ).grid(row=0, column=3, sticky='e', padx=(12, 0))
        
        # 2. Log Frame (Container)
        log_frame = ttk.Frame(tab)
        log_frame.grid(row=1, column=0, padx=10, pady=5, sticky='nsew')
        
        log_frame.grid_rowconfigure(0, weight=1)
        log_frame.grid_columnconfigure(0, weight=1)

        # 3. Text Area & Scrollbars
        self.log_text_extended = tk.Text(log_frame, state='normal', wrap='none', bg='white', font=("Consolas", 9))
        self.log_text_extended.grid(row=0, column=0, sticky='nsew')
        self._register_log_widget(self.log_text_extended)
        self.log_text_extended.bind(
            "<MouseWheel>",
            lambda e, w=self.log_text_extended: (self._scroll_start(w), self._schedule_scroll_end(w, delay_ms=350))
        )
        self.log_text_extended.bind("<ButtonPress-1>",  lambda e, w=self.log_text_extended: self._scroll_start(w))
        self.log_text_extended.bind("<ButtonRelease-1>", lambda e, w=self.log_text_extended: self._scroll_end(w, snap_if_bottom=True))
        # Go to bottom shortcut (Windows): Ctrl+End
        self.log_text_extended.bind("<Control-End>", lambda e: (self.log_text_extended.see(tk.END), "break"))
        self.log_text_extended.bind("<Control-Home>", lambda e: (self.log_text_extended.see("1.0"), "break"))  # optioneel
        
        # Scrollbars
        yscroll = ttk.Scrollbar(log_frame, orient='vertical', command=self.log_text_extended.yview)
        yscroll.grid(row=0, column=1, sticky='ns')
        
        yscroll.bind("<ButtonPress-1>",  lambda e, w=self.log_text_extended: self._scroll_start(w))
        yscroll.bind("<B1-Motion>",      lambda e, w=self.log_text_extended: self._scroll_start(w))
        yscroll.bind("<ButtonRelease-1>", lambda e, w=self.log_text_extended: self._scroll_end(w, snap_if_bottom=True))
        
        xscroll = ttk.Scrollbar(log_frame, orient='horizontal', command=self.log_text_extended.xview)
        xscroll.grid(row=1, column=0, sticky='ew')
        
        self.log_text_extended.configure(yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
        
        # Tags
        self.log_text_extended.tag_config('info', foreground='black')
        self.log_text_extended.tag_config('error', foreground='red')
        self.log_text_extended.tag_config('success', foreground='green')
        self.log_text_extended.tag_config('warning', foreground='#FF8C00')
        self.log_text_extended.tag_config('cmd', foreground='blue')
        # Nadir process color tags (P1..P4)
        self.log_text_extended.tag_config('nadir_p1', foreground='#ff4fa3')  # pink
        self.log_text_extended.tag_config('nadir_p2', foreground='#7b61ff')  # purple
        self.log_text_extended.tag_config('nadir_p3', foreground='#00a6a6')  # teal
        self.log_text_extended.tag_config('nadir_p4', foreground='#b06c2f')  # bronze
        
    def create_about_tab(self, tab):
        """Creates the About / Help tab content"""
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

        header_frame = tk.Frame(content, bg=self.system_bg_color, pady=20)
        header_frame.pack(fill='x')
        tk.Label(header_frame, text="GoPro Max & Hero Workflow Tool", font=('Arial', 20, 'bold'), bg=self.system_bg_color).pack()
        tk.Label(header_frame, text="Version 5.2.0 (Max 1 & 2 + Hero Edition)", font=('Arial', 10, 'bold'), fg='#666', bg=self.system_bg_color).pack()
        tk.Label(header_frame, text="Author: Michel / thewizard (Mapillary username)", font=('Arial', 9), fg='#666', bg=self.system_bg_color).pack()

        # --- CARD 1: MAX WORKFLOW ---
        card_max = create_card(content, "GoPro Max Workflow")
        msg_max = (    
        "This workflow processes GoPro Max 360° videos for Mapillary and/or Street View Studio (SVS). "
        "Max 1 and Max 2 files are detected automatically from .360 metadata, and mixed source videos are supported. "
        "The workflow handles GPMF extraction, video/metadata muxing and optional Nadir Patch processing. "
        )

        tk.Label(card_max, text=msg_max, bg='white', justify='left', anchor='w', wraplength=750).pack(fill='x', pady=(0, 10))
        
        grid_wf = tk.Frame(card_max, bg='white')
        grid_wf.pack(fill='x')
        grid_wf.grid_columnconfigure(0, weight=1)
        grid_wf.grid_columnconfigure(1, weight=1)

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
            "Nadir Patch (optional, Max workflow only): requires a PNG patch image and a working ImageMagick installation "
        )
        tk.Label(card_prep, text=msg_prep, bg='white', justify='left', anchor='w', wraplength=750).pack(fill='x', pady=(0, 10))

        # --- CARD 4: EXTERNAL TOOLS ---
        card_tools = create_card(content, "External Utilities")
        
        tk.Label(card_tools, 
                 text="Most tools (ExifTool, FFmpeg, FFprobe, and Mapillary Tools) are bundled. ImageMagick is only required when using the Nadir Patch feature.", 
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
     
    def _reset_analysis_cache(self):
        """Clears temporary per-run metadata/probe caches."""
        self._analysis_cache = {
            'ffprobe': {},
            'exiftool_json': {},
            'max_inventory': None
        }
     
    def _run_exiftool_json(self, file_path):
        """
        Reads metadata from a file using ExifTool and returns the first JSON object as a dict.
        Returns {} on failure.
        Results are cached for the lifetime of the current workflow run.
        """
        cache_key = str(Path(file_path).resolve())
        cached = self._analysis_cache.get('exiftool_json', {}).get(cache_key)
        if cached is not None:
            return dict(cached) if isinstance(cached, dict) else {}

        command = [
            self.settings['ExifToolPath'],
            '-j',
            '-G1',
            '-s',
            str(file_path)
        ]

        rc, out = self.run_command(command, error_message=f"ExifTool failed for {file_path}")
        if rc != 0 or not out.strip():
            self._analysis_cache.setdefault('exiftool_json', {})[cache_key] = {}
            return {}

        try:
            data = json.loads(out)
            if isinstance(data, list) and data:
                meta = data[0] if isinstance(data[0], dict) else {}
                self._analysis_cache.setdefault('exiftool_json', {})[cache_key] = dict(meta)
                return dict(meta)
        except Exception:
            pass

        self._analysis_cache.setdefault('exiftool_json', {})[cache_key] = {}
        return {}

    def _detect_max_family_from_metadata(self, meta):
        """
        Detects the Max processing family from ExifTool metadata.
        Returns: 'max1', 'max2', or 'unknown'
        """
        model = str(meta.get('GoPro:Model') or '').strip().upper()
        firmware = str(
            meta.get('GoPro:FirmwareVersion')
            or meta.get('UserData:FirmwareVersion')
            or ''
        ).strip().upper()

        video_frame_size = str(meta.get('GoPro:VideoFrameSize') or '').strip()
        track_w = int(meta.get('Track1:ImageWidth') or 0)
        track_h = int(meta.get('Track1:ImageHeight') or 0)

        # Primary identification
        if model == 'MAX2':
            return 'max2'

        if model == 'GOPRO MAX':
            return 'max1'

        # Fallback on firmware family
        if firmware.startswith('H24'):
            return 'max2'

        if firmware.startswith('H19'):
            return 'max1'

        # Fallback on image/video size
        if video_frame_size == '5952x1920' or (track_w, track_h) == (5952, 1920):
            return 'max2'

        if video_frame_size == '4096x1344' or (track_w, track_h) == (4096, 1344):
            return 'max1'

        return 'unknown'

    def _detect_max_family_for_360(self, original_360_path):
        """
        Detects the Max family for a .360 source file.
        Returns a tuple: (family, metadata_dict)
        """
        meta = self._run_exiftool_json(original_360_path)
        family = self._detect_max_family_from_metadata(meta)
        return family, meta
        
    def _metadata_has_audio_tracks(self, meta: dict) -> bool:
        """
        Returns True when the ExifTool metadata indicates one or more audio tracks.

        This is used as a sanity-check for legacy / inconsistent Max 1 files where
        GoPro:Rate may report a Time Lapse-style value even though the file behaves
        like a normal video recording.
        """
        if not isinstance(meta, dict):
            return False

        for key, value in meta.items():
            key_text = str(key)
            value_text = str(value).strip().lower()

            if key_text.endswith(":HandlerType") and value_text == "audio track":
                return True

            if ":AudioFormat" in key_text or ":AudioChannels" in key_text:
                return True
    
    def _apply_max1_time_mode_override(self, family: str, meta: dict, time_mode_info: dict) -> dict:
        """
        Applies a targeted override for Max 1 files that are falsely identified as
        Time Lapse based only on the GoPro Rate tag.

        Rule:
        - If family == max1
        - and parsed mode == timelapse
        - and the .360 metadata clearly contains audio tracks
        then treat the file as standard video instead of Time Lapse.
        """
        result = dict(time_mode_info or {})
        result.setdefault("override_reason", None)

        if family != "max1":
            return result

        if result.get("mode") != "timelapse":
            return result

        if not self._metadata_has_audio_tracks(meta):
            return result

        raw_rate = result.get("raw_rate")
        result["mode"] = "standard"
        result["timewarp_rate"] = None
        result["supported"] = True
        result["reason"] = None
        result["effective_unique_fps"] = None
        result["override_reason"] = (
            f"Max 1 override applied: GoPro Rate={raw_rate}, but audio tracks were detected "
            f"in the .360 metadata, so the file is treated as standard video instead of Time Lapse."
        )

        return result
    
    def validate_runtime_deep_max(self):
        """
        Heavy validation for Max workflow.
        Runs in worker thread only.
        Returns (valid, inventory)
        """
        valid = True

        inv = self._get_max_inventory(
            log_selection=False,
            log_warnings=True,
            log_detection=True,
            force_refresh=True
        )

        if not inv["all_360"]:
            self.log_message("[FATAL] No .360 files found in Max Source Location.", 'error')
            valid = False

        if not inv["all_videos"]:
            self.log_message("[FATAL] No .mp4/.mov files found in Max Source Location.", 'error')
            valid = False

        if inv["all_360"] and inv["all_videos"] and not inv["matched_pairs"]:
            self.log_message(
                "[FATAL] No matching .360 + .mp4/.mov filename pairs found in Max Source Location.",
                'error'
            )
            valid = False

        counts = inv.get("family_counts", {})
        self.log_message(
            f"[FAMILY SUMMARY] Max 1={counts.get('max1', 0)} | "
            f"Max 2={counts.get('max2', 0)} | "
            f"Unknown={counts.get('unknown', 0)}",
            'info'
        )

        if counts.get('unknown', 0) > 0 and self.workflow_choice.get() in [2, 3]:
            self.log_message(
                "[FATAL] One or more matched .360 files could not be classified as Max 1 or Max 2. "
                "SVS / Run all requires a known family.",
                'error'
            )
            valid = False
        elif counts.get('unknown', 0) > 0:
            self.log_message(
                "[WARNING] One or more matched .360 files could not be classified as Max 1 or Max 2. "
                "Mapillary-only may continue, but review detection output carefully.",
                'warning'
            )
            
        # --- Time mode analysis state ---
        self.detected_timewarp_items = []
        self.unsupported_time_mode_items = []
        self.accepted_time_mode_items = []
        self.rejected_time_mode_items = []

        for item in inv["matched_items"]:
            if item.get("time_mode") == "timewarp":
                self.detected_timewarp_items.append(item)

            if item.get("time_mode_supported", True):
                self.accepted_time_mode_items.append(item)
            else:
                self.unsupported_time_mode_items.append(item)
                self.rejected_time_mode_items.append(item)

        inv["accepted_items"] = list(self.accepted_time_mode_items)
        inv["rejected_items"] = list(self.rejected_time_mode_items)

        supported_timewarp_items = [
            item for item in self.accepted_time_mode_items
            if item.get("time_mode") == "timewarp"
        ]

        if supported_timewarp_items:
            self.log_message("", 'info')
            self.log_message("[TIME MODE] Supported TimeWarp source files detected:", 'info')

            for item in supported_timewarp_items:
                self.log_message(
                    f"  - {item['video_source'].name}: {self._format_time_mode_summary(item)}",
                    'info'
                )

        if self.rejected_time_mode_items:
            self.log_message("", 'info')
            self.log_message("[TIME MODE] Unsupported time-based source content will be skipped:", 'warning')

            for item in self.rejected_time_mode_items:
                self.log_message(
                    f"  - {item['video_source'].name}: {self._format_time_mode_summary(item)}",
                    'warning'
                )
                self.log_message(
                    f"    Reason: {item.get('time_mode_reason') or 'Unsupported time-based mode.'}",
                    'warning'
                )

        if not self.accepted_time_mode_items:
            self.log_message("", 'info')
            self.log_message(
                "[FATAL] No supported files remain after TimeWarp / Time Lapse validation.",
                'error'
            )
            self.log_message(
                "Workflow aborted. Only standard video and TimeWarp 2X / 5X can continue.",
                'error'
            )
            valid = False
           
        if valid:
            self.log_message("Deep validation OK.", 'success')

        return valid, inv
    
    def _build_max_source_inventory(self, log_selection=False, log_warnings=False, log_detection=False):
        """
        Builds an inventory of Max source files based on matching stems:
        - .360 originals
        - preferred .mp4/.mov video per stem
        - detected family per matched pair

        Returns a dict with:
            all_360        -> list[Path]
            all_videos     -> list[Path]
            matched_pairs  -> list[tuple(stem, original_360_path, video_path)]
            matched_items  -> list[dict]
            orphan_360     -> list[Path]
            orphan_videos  -> list[Path]
            family_counts  -> dict
        """
        source_dir = Path(self.settings['SourceDir'])
        if not source_dir.is_dir():
            return {
                "all_360": [],
                "all_videos": [],
                "matched_pairs": [],
                "matched_items": [],
                "orphan_360": [],
                "orphan_videos": [],
                "family_counts": {"max1": 0, "max2": 0, "unknown": 0}
            }

        # 1) Collect all .360 originals by stem
        original_360_by_stem = {}
        for p in source_dir.glob("*.360"):
            original_360_by_stem[p.stem] = p

        # 2) Collect candidate .mp4/.mov files
        candidates = []
        for pattern in ("*.mp4", "*.mov"):
            for p in source_dir.glob(pattern):
                name_lower = p.name.lower()
                if name_lower.endswith("_gpmf.mov"):
                    continue
                if name_lower.endswith("_gpmf_final.mov"):
                    continue
                candidates.append(p)

        # 3) Group videos by stem and choose preferred source per stem
        grouped = {}
        for p in candidates:
            grouped.setdefault(p.stem, []).append(p)

        selected_video_by_stem = {}

        for stem, files in grouped.items():
            scored = []

            for f in files:
                info = self._probe_video_stream_info(f)
                codec = self._classify_video_codec(info)

                if codec == "cineform":
                    score = 300
                elif codec == "hevc":
                    score = 200
                elif codec == "h264":
                    score = 100
                else:
                    score = 0

                bitrate = info.get("bit_rate") if info else 0
                bitrate = bitrate or 0
                scored.append((score, bitrate, f, codec))

            scored.sort(key=lambda x: (x[0], x[1]), reverse=True)
            best = scored[0]
            best_file = best[2]
            best_codec = best[3]

            selected_video_by_stem[stem] = best_file

            if log_selection:
                self.log_message(f"[SOURCE SELECT] {stem} -> using {best_file.name} ({best_codec}).", 'info')

        # 4) Stem matching
        stems_360 = set(original_360_by_stem.keys())
        stems_video = set(selected_video_by_stem.keys())

        matched_stems = sorted(stems_360 & stems_video)
        orphan_360_stems = sorted(stems_360 - stems_video)
        orphan_video_stems = sorted(stems_video - stems_360)

        matched_pairs = [
            (stem, original_360_by_stem[stem], selected_video_by_stem[stem])
            for stem in matched_stems
        ]
        orphan_360 = [original_360_by_stem[stem] for stem in orphan_360_stems]
        orphan_videos = [selected_video_by_stem[stem] for stem in orphan_video_stems]

        # 5) Detect family per matched pair
        matched_items = []
        family_counts = {"max1": 0, "max2": 0, "unknown": 0}

        for stem, original_360, video_path in matched_pairs:
            family, meta = self._detect_max_family_for_360(original_360)
            family_counts[family] = family_counts.get(family, 0) + 1

            time_mode_info = self._analyze_time_mode_for_video(original_360, video_path)
            time_mode_info = self._apply_max1_time_mode_override(family, meta, time_mode_info)

            item = {
                "stem": stem,
                "original_360": original_360,
                "video_source": video_path,
                "family": family,
                "meta": meta,

                "time_mode": time_mode_info["mode"],
                "time_mode_raw_rate": time_mode_info["raw_rate"],
                "timewarp_rate": time_mode_info["timewarp_rate"],
                "time_mode_output_fps": time_mode_info["output_fps"],
                "time_mode_effective_unique_fps": time_mode_info["effective_unique_fps"],
                "time_mode_supported": time_mode_info["supported"],
                "time_mode_reason": time_mode_info["reason"],
                "time_mode_override_reason": time_mode_info.get("override_reason"),
            }

            matched_items.append(item)

            if log_detection:
                self.log_message(
                    f"[FAMILY DETECT] {stem} -> {family.upper()} "
                    f"(Model={meta.get('GoPro:Model', 'n/a')}, "
                    f"Firmware={meta.get('GoPro:FirmwareVersion', meta.get('UserData:FirmwareVersion', 'n/a'))})",
                    'info'
                )

                if item.get("time_mode_override_reason"):
                    self.log_message(
                        f"[TIME MODE OVERRIDE] {stem} -> Standard video | {item['time_mode_override_reason']}",
                        'warning'
                    )
                elif item["time_mode"] != "standard":
                    level = 'info' if item.get("time_mode_supported", True) else 'warning'
                    self.log_message(
                        f"[TIME MODE DETECT] {stem} -> {self._format_time_mode_summary(item)} "
                        f"| Supported={item.get('time_mode_supported', True)}",
                        level
                    )

        if log_warnings:
            for p in orphan_360:
                self.log_message(
                    f"[SOURCE WARNING] {p.name} skipped: no matching .mp4/.mov found with the same base name.",
                    'warning'
                )

            for p in orphan_videos:
                self.log_message(
                    f"[SOURCE WARNING] {p.name} skipped: no matching .360 found with the same base name.",
                    'warning'
                )

        return {
            "all_360": sorted(original_360_by_stem.values()),
            "all_videos": sorted(selected_video_by_stem.values()),
            "matched_pairs": matched_pairs,
            "matched_items": matched_items,
            "orphan_360": orphan_360,
            "orphan_videos": orphan_videos,
            "family_counts": family_counts
        }
        
    def _get_max_inventory(
        self,
        log_selection=False,
        log_warnings=False,
        log_detection=False,
        force_refresh=False
    ):
        """
        Returns Max source inventory with smart reuse:
        1) use validated inventory from deep validation when available
        2) otherwise use cached non-logging inventory
        3) otherwise rebuild

        Notes:
        - If any logging flags are enabled, we rebuild unless force_refresh is False
          and a validated inventory already exists.
        - Only non-logging inventories are stored in _analysis_cache['max_inventory'].
        """
        # 1) Prefer the already validated inventory from deep validation
        validated = self.settings.get('_validated_inventory')
        if validated is not None and not force_refresh:
            if not log_selection and not log_warnings and not log_detection:
                return validated

        # 2) Use cached non-logging inventory when possible
        cached = self._analysis_cache.get('max_inventory')
        if cached is not None and not force_refresh:
            if not log_selection and not log_warnings and not log_detection:
                return cached

        # 3) Rebuild inventory
        inv = self._build_max_source_inventory(
            log_selection=log_selection,
            log_warnings=log_warnings,
            log_detection=log_detection
        )

        # Only cache silent inventories
        if not log_selection and not log_warnings and not log_detection:
            self._analysis_cache['max_inventory'] = inv

        return inv
        
    def _collect_matched_max_items(self, family=None):
        inv = self._get_max_inventory(
            log_selection=False,
            log_warnings=False,
            log_detection=False
        )
        items = inv["matched_items"]
        if family:
            items = [x for x in items if x["family"] == family]
        return items


    def _collect_matched_max_360_files(self, family=None):
        items = self._collect_matched_max_items(family=family)
        return [item["original_360"] for item in items]

    def _collect_preferred_max_source_files(self, family=None):
        """
        Returns only preferred .mp4/.mov files that have a matching .360 file
        with the same base name, optionally filtered by family.
        """
        items = self._collect_matched_max_items(family=family)
        return [item["video_source"] for item in items]

    def _filter_intermediate_mov_files(self, mov_files, items, custom_suffix=""):
        """
        Filters *_gpmf_final.mov files so only stems belonging to the given items remain.
        """
        allowed_stems = {item["stem"] for item in items}
        filtered = []

        for p in mov_files:
            stem = p.stem.removesuffix('_gpmf_final')
            if custom_suffix:
                stem = stem.removesuffix(custom_suffix)
            if stem in allowed_stems:
                filtered.append(p)

        return sorted(filtered)
    
    def _has_max_360_source_files(self):
        inv = self._get_max_inventory(
            log_selection=False,
            log_warnings=False,
            log_detection=False
        )
        return bool(inv["all_360"])

    def _has_max_mp4_mov_source_files(self):
        inv = self._get_max_inventory(
            log_selection=False,
            log_warnings=False,
            log_detection=False
        )
        return bool(inv["all_videos"])

    def _has_matching_max_source_pairs(self):
        inv = self._get_max_inventory(
            log_selection=False,
            log_warnings=False,
            log_detection=False
        )
        return bool(inv["matched_pairs"])

    def _has_hero_mp4_files(self):
        """Checks whether the Hero Source Location contains at least one .mp4 file."""
        source_dir = Path(self.settings['HeroSourceDir'])
        if not source_dir.is_dir():
            return False
        return any(source_dir.glob("*.mp4"))

    def validate_runtime_quick(self, mode):
        """Fast validation that is safe to run on the GUI thread."""
        self.update_settings_dict()
        self.log_text.delete('1.0', tk.END)
        self.log_message(f"--- QUICK VALIDATING FOR {mode.upper()} ---", 'info')

        valid = True

        if mode == 'max':
            choice = self.workflow_choice.get()
            need_mapillary = (choice in [1, 3])

            if not Path(self.settings['SourceDir']).is_dir():
                self.log_message("[FATAL] Max Source invalid.", 'error')
                valid = False

            if not Path(self.settings['TargetDir']).is_dir():
                self.log_message("[FATAL] Max Target invalid.", 'error')
                valid = False

            if not Path(self.settings['FFmpegPath']).is_file():
                self.log_message("[FATAL] FFmpeg missing or path invalid.", 'error')
                valid = False

            if not Path(self.settings['FFprobePath']).is_file():
                self.log_message("[FATAL] FFprobe missing or path invalid.", 'error')
                valid = False

            if not Path(self.settings['ExifToolPath']).is_file():
                self.log_message("[FATAL] ExifTool missing or path invalid.", 'error')
                valid = False

            if need_mapillary:
                if not Path(self.settings['MapillaryToolsPath']).is_file():
                    self.log_message("[FATAL] Mapillary Tools missing or path invalid.", 'error')
                    valid = False

                if not self.settings['MapillaryUserName'].strip():
                    self.log_message("[FATAL] Mapillary Profile Name is empty.", 'error')
                    valid = False

                try:
                    if float(self.settings['VideoSampleDistance']) <= 0:
                        self.log_message("[FATAL] Sample Distance must be greater than 0.", 'error')
                        valid = False
                except Exception:
                    self.log_message("[FATAL] Sample Distance is invalid.", 'error')
                    valid = False

                try:
                    if int(self.settings['MapillaryUploadWorkers']) < 1:
                        self.log_message("[FATAL] Upload Workers must be at least 1.", 'error')
                        valid = False
                except Exception:
                    self.log_message("[FATAL] Upload Workers value is invalid.", 'error')
                    valid = False

        elif mode == 'hero':
            # laat hero voorlopig zoals nu, of maak hier ook een quick-only variant
            return self.validate_runtime('hero')

        else:
            self.log_message(f"[FATAL] Unknown validation mode: {mode}", 'error')
            valid = False

        if valid:
            self.log_message("Quick validation OK.", 'success')

        return valid

    def validate_runtime(self, mode):
        """Hard validation before starting a workflow."""

        if mode == 'max':
            return self.validate_runtime_quick('max')

        self.update_settings_dict()
        self.log_text.delete('1.0', tk.END)
        self.log_message(f"--- VALIDATING FOR {mode.upper()} ---", 'info')

        valid = True

        if mode == 'hero':
            # Basic folder validation
            if not Path(self.settings['HeroSourceDir']).is_dir():
                self.log_message("[FATAL] Hero Source invalid.", 'error')
                valid = False

            if not Path(self.settings['HeroTargetDir']).is_dir():
                self.log_message("[FATAL] Hero Target invalid.", 'error')
                valid = False

            # Hero source must contain mp4 files
            if not self._has_hero_mp4_files():
                self.log_message("[FATAL] No .mp4 files found in Hero Source Location.", 'error')
                valid = False

            # Mapillary Tools are required for Hero workflow
            if not Path(self.settings['MapillaryToolsPath']).is_file():
                self.log_message("[FATAL] Mapillary Tools missing or path invalid.", 'error')
                valid = False

            if not self.settings['MapillaryUserName'].strip():
                self.log_message("[FATAL] Mapillary Profile Name is empty.", 'error')
                valid = False

            try:
                if float(self.settings['VideoSampleDistance']) <= 0:
                    self.log_message("[FATAL] Sample Distance must be greater than 0.", 'error')
                    valid = False
            except Exception:
                self.log_message("[FATAL] Sample Distance is invalid.", 'error')
                valid = False

            try:
                if int(self.settings['MapillaryUploadWorkers']) < 1:
                    self.log_message("[FATAL] Upload Workers must be at least 1.", 'error')
                    valid = False
            except Exception:
                self.log_message("[FATAL] Upload Workers value is invalid.", 'error')
                valid = False

        else:
            self.log_message(f"[FATAL] Unknown validation mode: {mode}", 'error')
            valid = False

        if valid:
            self.log_message("Validation OK.", 'success')

        return valid

    def start_max_workflow(self):
        self._reset_analysis_cache()
        self.notebook.select(self.log_tab)

        if not self.validate_runtime_quick('max'):
            return

        self.update_flags_from_ui()
        
        # --- LOGIC MODIFICATION FOR UPLOAD ONLY (MAX) ---
        # Check the variable (self.mapillary_actions_var) used in the GUI
        act = self.mapillary_actions_var.get()
        
        if self.workflow_choice.get() == 2:
            self.settings['RunUpload'] = False
            self.settings['RunSample'] = False

        elif act == 3: # Upload Only
            self.settings['RunCorePrep'] = False # Skip 360 conversion
            self.settings['RunSample'] = False   # Skip Sampling
            self.settings['RunProcess'] = True   # Enable Processing
            self.settings['RunUpload'] = True    # Enable Upload
        else:
            # Maintain standard logic based on UI flags, but ensure Upload follows the radio button
            # (Assuming update_flags_from_ui handles CorePrep/Sample/Process defaults)
            self.settings['RunUpload'] = (act == 1)

        if self.running_thread and self.running_thread.is_alive():
             self.log_message("[FATAL] Another workflow is already running. Please stop it first.", 'error')
             messagebox.showerror("Runtime Error", "Another workflow is currently active.")
             return
        
        # --- THREAD CONTROL INIT ---
        self.stop_event.clear()
        self.set_stop_button_state(tk.NORMAL)
         
        workflow_thread = threading.Thread(target=self._validate_and_run_max_workflow)
        self.running_thread = workflow_thread
        workflow_thread.start()


    def start_hero_workflow(self):
        self._reset_analysis_cache()
        self.notebook.select(self.log_tab)

        if not self.validate_runtime('hero'):
            return
        
        if self.running_thread and self.running_thread.is_alive():
             self.log_message("[FATAL] Another workflow is already running. Please stop it first.", 'error')
             messagebox.showerror("Runtime Error", "Another workflow is currently active.")
             return

        # --- DETERMINE ACTION FLAGS ---
        act = self.hero_mapillary_actions_var.get()
        
        if act == 3: # Upload Only
            self.settings['RunSample'] = False
            self.settings['RunProcess'] = True
            self.settings['RunUpload'] = True
        else: # 1 (Sample/Process/Upload) or 2 (Sample/Process Only)
            self.settings['RunSample'] = True
            self.settings['RunProcess'] = True
            self.settings['RunUpload'] = (act == 1)
        
        # --- THREAD CONTROL INIT ---
        self.stop_event.clear()
        self.set_stop_button_state(tk.NORMAL)

        workflow_thread = threading.Thread(target=self.run_hero_workflow_logic)
        self.running_thread = workflow_thread
        workflow_thread.start()
        
    def _cleanup_after_workflow(self):
        """Common cleanup steps after workflow completes or is aborted."""
        self.set_stop_button_state(tk.DISABLED)
        self.running_thread = None 
        self.stop_event.clear() 

    def stop_workflow(self):
        """Signals the running thread to stop gracefully."""
        if self.running_thread and self.running_thread.is_alive():
            self.stop_event.set() 
            self.log_message("\n[WARNING] STOP signal received. Aborting workflow at next safe point...", 'error')
            
            self.set_stop_button_state(tk.DISABLED)
        else:
            self.log_message("[INFO] No active workflow thread found.", 'info')
    
    def _update_progress_ui(self, current_step, total_steps):
        """
        Performs the actual progress bar update on the Tkinter main thread.
        Returns the calculated percentage.
        """
        if hasattr(self, 'progress_bar') and self.progress_bar is not None and total_steps > 0:
            percentage = (current_step / total_steps) * 100
            self.progress_bar['value'] = percentage
            self.master.update_idletasks()
            return percentage
        return 0
    
    def update_progress(self, current_step, total_steps):
        """
        Thread-safe progress update entry point.
        If called from the main thread, update directly.
        If called from a worker thread, queue the progress update for UI processing.
        Returns the calculated percentage for caller logic.
        """
        if threading.current_thread() is threading.main_thread():
            return self._update_progress_ui(current_step, total_steps)
        else:
            self.ui_queue.put(("progress", current_step, total_steps))
            if total_steps > 0:
                return (current_step / total_steps) * 100
            return 0
        
    def set_stop_button_state(self, state):
        """
        Thread-safe stop button state update.
        If called from the main thread, update directly.
        If called from a worker thread, queue the state change.
        """
        if threading.current_thread() is threading.main_thread():
            if self.stop_button:
                self.stop_button.config(state=state)
        else:
            self.ui_queue.put(("stop_button", state))
    
    def show_messagebox(self, level, title, message):
        """
        Thread-safe messagebox helper.
        If called from the main thread, show the messagebox directly.
        If called from a worker thread, queue the messagebox event for UI processing.
        """
        if threading.current_thread() is threading.main_thread():
            if level == "info":
                messagebox.showinfo(title, message)
            elif level == "warning":
                messagebox.showwarning(title, message)
            elif level == "error":
                messagebox.showerror(title, message)
        else:
            self.ui_queue.put(("messagebox", level, title, message))
    
    def check_for_abort(self, step_name):
        """Checks the stop flag and raises an exception if set."""
        if self.stop_event.is_set():
            raise UserAbortException(f"Workflow manually stopped during {step_name}.")
        return False
            
    def _get_first_gpx_time_for_fixer(self, gpx_path: Path):
        """
        Returns the first valid, non-empty GPX timestamp for SVS header fixing.

        Important:
        - Some GPX files may start with one or more <trkpt> entries where <time>
          is present but empty.
        - Therefore we must scan for the first non-empty, parseable timestamp
          instead of blindly reading the first <time> element.
        """
        if not gpx_path.is_file():
            self.log_message(f"    [ERROR] SVS Fix: GPX file not found at: {gpx_path}", 'error')
            return None, None

        try:
            tree = ET.parse(gpx_path)
            root = tree.getroot()

            time_elements = root.findall(f'.//{{{GPX_NAMESPACE_URI}}}trkpt/{{{GPX_NAMESPACE_URI}}}time')
            if not time_elements:
                time_elements = root.findall(f'.//{{{GPX_NAMESPACE_URI}}}time')

            first_valid_time_str = None

            for time_element in time_elements:
                if time_element is None:
                    continue

                raw_text = time_element.text
                if raw_text is None:
                    continue

                raw_text = raw_text.strip()
                if not raw_text:
                    continue

                try:
                    dt_obj = self._parse_gpx_iso_datetime(raw_text)
                    first_valid_time_str = raw_text
                    break
                except Exception:
                    continue

            if not first_valid_time_str:
                self.log_message(
                    f"    [ERROR] SVS Fix: No valid non-empty <time> tag found in {gpx_path.name}.",
                    'error'
                )
                return None, None

            dt_obj = self._parse_gpx_iso_datetime(first_valid_time_str)
            exiftool_time_format = dt_obj.strftime("%Y:%m:%d %H:%M:%S")

            self.log_message(
                f"    [INFO] SVS Fix: Found first valid GPX Start Time: {first_valid_time_str}",
                'info'
            )
            return first_valid_time_str, exiftool_time_format

        except Exception as e:
            self.log_message(
                f"    [ERROR] SVS Fix: Error reading GPX start time for {gpx_path.name}: {e}",
                'error'
            )
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
        """
        Detects video stream bit depth (8, 10, or 12) using FFprobe.
        Robustly handles 'N/A' outputs by checking the pixel format.
        """
        cmd = [
            self.settings['FFprobePath'], 
            "-v", "error", 
            "-select_streams", "v:0", 
            "-show_entries", "stream=bits_per_raw_sample:stream=pix_fmt", 
            "-of", "csv=p=0:nk=1", # Output example: "10,yuv420p10le" or "yuv420p10le,N/A,"
            str(path)
        ]
        
        c, o = self.run_command(cmd)
        default_depth = 8
        
        if c == 0 and o.strip():
            # Split by comma and remove empty whitespace strings
            parts = [p.strip() for p in o.strip().split(',') if p.strip()] 
            
            for part in parts:
                # 1. Check for explicit number (e.g., "10")
                if part.isdigit():
                    val = int(part)
                    if val >= 8: return val
                
                # 2. Check Pixel Format for hints (e.g., "yuv420p10le" -> p10 = 10bit)
                if "p10" in part:
                     self.log_message(f"    [INFO] Determined 10-bit depth via pixel format ({part}).", 'info')
                     return 10
                if "p12" in part:
                     self.log_message(f"    [INFO] Determined 12-bit depth via pixel format ({part}).", 'info')
                     return 12
        
        self.log_message(f"    [INFO] Bit-depth tag not detected (Normal for GoPro Max). Defaulting to 8-bit.", 'info')
        return default_depth

    def _get_video_dims(self, path):
        """
        Retrieves video resolution (Width, Height).
        Uses Regex to ignore trailing delimiters (fixes '7680x3840x' issue).
        """
        cmd = [
            self.settings['FFprobePath'], 
            "-v", "error", 
            "-select_streams", "v:0", 
            "-show_entries", "stream=width,height", 
            "-of", "csv=p=0:s=x", # Output example: "7680x3840" or "7680x3840x"
            str(path)
        ]
        
        c, o = self.run_command(cmd)
        
        if c == 0 and o:
            # Regex is safer here than splitting because it ignores the trailing 'x' automatically
            # It looks for NUMBER x NUMBER
            m = re.search(r"(\d+)x(\d+)", o)
            if m:
                return int(m.group(1)), int(m.group(2))
                
        return None, None
    
    def _get_video_fps(self, video_path: Path) -> float:
        """
        Returns the video's FPS as a float using ffprobe.
        Prefers avg_frame_rate, falls back to r_frame_rate.
        Returns 0.0 if it cannot be determined.
        """
        try:
            info = self._probe_video_stream_info(video_path)  # existing helper returns stream dict
            if not info:
                return 0.0

            def _parse_ratio(x):
                if not x:
                    return 0.0
                if isinstance(x, (int, float)):
                    return float(x)
                s = str(x).strip()
                if '/' in s:
                    num, den = s.split('/', 1)
                    num = float(num)
                    den = float(den)
                    return num / den if den != 0 else 0.0
                return float(s)

            # _probe_video_stream_info already returns a numeric FPS in info["fps"]
            fps = float(info.get("fps") or 0.0)

            # Safety clamp (avoid ridiculous values)
            if fps < 1.0 or fps > 240.0:
                return 0.0

            return fps

        except Exception:
            return 0.0
            
    def _read_gopro_rate_tag(self, media_path: Path):
        """
        Reads the GoPro 'Rate' tag via ExifTool JSON metadata.

        Expected examples:
            TimeWarp: 2X, 5X, 10X, 30X
            Time Lapse: 2_1SEC, 0_5SEC

        Returns the first non-empty value or None.
        """
        cmd = [
            self.settings['ExifToolPath'],
            "-j",
            "-G1",
            "-s",
            "-GoPro:Rate",
            str(media_path)
        ]

        rc, out = self.run_command(
            cmd,
            error_message=f"ExifTool Rate read failed for {media_path}"
        )

        if rc != 0 or not out:
            return None

        try:
            data = json.loads(out)
            if not data or not isinstance(data, list):
                return None

            row = data[0]
            if not isinstance(row, dict):
                return None

            return row.get("GoPro:Rate") or row.get("Rate")

        except Exception:
            return None

    def _parse_gopro_time_mode(self, rate_value):
        """
        Parses GoPro Rate values into a normalized structure.

        Examples:
            2X      -> timewarp, rate=2
            5X      -> timewarp, rate=5
            2_1SEC  -> timelapse
            0_5SEC  -> timelapse
        """
        result = {
            "raw_rate": rate_value,
            "mode": "standard",
            "timewarp_rate": None,
            "supported": True,
            "reason": None,
        }

        if not rate_value:
            return result

        rv = str(rate_value).strip().upper()

        if rv.endswith("X"):
            result["mode"] = "timewarp"
            try:
                result["timewarp_rate"] = int(rv[:-1])
            except ValueError:
                result["supported"] = False
                result["reason"] = f"Invalid TimeWarp rate value detected: {rate_value}"
            return result

        if "_" in rv or "SEC" in rv:
            result["mode"] = "timelapse"
            result["supported"] = False
            result["reason"] = (
                f"Time Lapse mode detected ({rate_value}). "
                "Time Lapse is not supported by this workflow for SVS/Mapillary processing."
            )
            return result

        return result


    def _analyze_time_mode_for_video(self, metadata_path: Path, fps_source_path: Path):
        """
        Performs full TimeWarp / Time Lapse analysis.

        metadata_path:
            path used to read the GoPro Rate tag (preferably the .360 original)

        fps_source_path:
            path used to read the actual output FPS (the preferred .mp4/.mov source)

        Returns dict:
            {
                raw_rate,
                mode,
                timewarp_rate,
                output_fps,
                effective_unique_fps,
                supported,
                reason
            }
        """
        parsed = self._parse_gopro_time_mode(self._read_gopro_rate_tag(metadata_path))

        result = {
            "raw_rate": parsed["raw_rate"],
            "mode": parsed["mode"],
            "timewarp_rate": parsed["timewarp_rate"],
            "output_fps": None,
            "effective_unique_fps": None,
            "supported": parsed["supported"],
            "reason": parsed["reason"],
        }

        if parsed["mode"] != "timewarp":
            return result

        output_fps = self._get_video_fps(fps_source_path)
        result["output_fps"] = output_fps

        if not output_fps or output_fps <= 0:
            result["supported"] = False
            result["reason"] = (
                "TimeWarp detected, but the actual output frame rate could not be determined."
            )
            return result

        if not parsed["timewarp_rate"]:
            result["supported"] = False
            result["reason"] = (
                f"TimeWarp detected, but the rate value is invalid ({parsed['raw_rate']})."
            )
            return result

        result["effective_unique_fps"] = output_fps / parsed["timewarp_rate"]

        if parsed["timewarp_rate"] not in (2, 5):
            result["supported"] = False
            result["reason"] = (
                f"Unsupported TimeWarp mode detected: {parsed['timewarp_rate']}X "
                f"({output_fps:.2f} fps output => "
                f"{result['effective_unique_fps']:.2f} effective fps). "
                "Only TimeWarp 2X and 5X are supported."
            )

        return result

    def _format_time_mode_summary(self, item):
        """
        Returns a short human-readable summary for logging.
        """
        mode = item.get("time_mode", "standard")
        raw_rate = item.get("time_mode_raw_rate")
        output_fps = item.get("time_mode_output_fps")
        effective_fps = item.get("time_mode_effective_unique_fps")

        output_fps_txt = f"{output_fps:.2f}" if isinstance(output_fps, (int, float)) and output_fps > 0 else "n/a"
        effective_fps_txt = f"{effective_fps:.2f}" if isinstance(effective_fps, (int, float)) and effective_fps > 0 else "n/a"

        if mode == "timewarp":
            return (
                f"TimeWarp {item.get('timewarp_rate')}X "
                f"(Rate={raw_rate}, Video FPS={output_fps_txt}, "
                f"Effective FPS={effective_fps_txt})"
            )

        if mode == "timelapse":
            return f"Time Lapse (Rate={raw_rate})"

        return "Standard video mode"
        
    def _get_time_mode_accept_reason(self, item):
        """
        Returns the accept reason for a supported item.
        """
        mode = item.get("time_mode", "standard")
        output_fps = item.get("time_mode_output_fps")
        effective_fps = item.get("time_mode_effective_unique_fps")

        output_fps_txt = f"{output_fps:.2f}" if isinstance(output_fps, (int, float)) and output_fps > 0 else "n/a"
        effective_fps_txt = f"{effective_fps:.2f}" if isinstance(effective_fps, (int, float)) and effective_fps > 0 else "n/a"

        if mode == "timewarp":
            return (
                f"Supported TimeWarp mode: {item.get('timewarp_rate')}X "
                f"({output_fps_txt} fps output => {effective_fps_txt} effective fps)."
            )

        return "Standard video mode accepted."


    def _build_accept_reject_summary_text(self, processed_items, rejected_items):
        """
        Builds a plain-text summary for the final messagebox.
        """
        lines = []

        lines.append("Processed / Accepted:")
        if processed_items:
            for item in processed_items:
                lines.append(f"- {item['video_source'].name}")
                lines.append(f"  Reason: {self._get_time_mode_accept_reason(item)}")
        else:
            lines.append("- None")

        lines.append("")
        lines.append("Rejected / Skipped:")
        if rejected_items:
            for item in rejected_items:
                lines.append(f"- {item['video_source'].name}")
                lines.append(f"  Mode: {self._format_time_mode_summary(item)}")
                lines.append(
                    f"  Reason: {item.get('time_mode_reason') or 'Unsupported time-based mode.'}"
                )
        else:
            lines.append("- None")

        return "\n".join(lines)


    def _log_accept_reject_summary(self, processed_items, rejected_items, orphan_360=None, orphan_videos=None):
        """
        Writes a color-emphasized final summary to the Output Log.

        Included sections:
        - accepted / processed items
        - rejected / skipped items
        - unmatched source files (.360 without video, or video without .360),
          but ONLY when such files actually exist
        """
        orphan_360 = orphan_360 or []
        orphan_videos = orphan_videos or []

        self.log_message("", 'info')
        self.log_message("=======================================================", 'info')
        self.log_message(" FINAL ACCEPT / REJECT SUMMARY", 'info')
        self.log_message("=======================================================", 'info')

        self.log_message("[ACCEPTED / PROCESSED]", 'success')
        if processed_items:
            for item in processed_items:
                self.log_message(f"  - {item['video_source'].name}", 'success')
                self.log_message(f"    Reason: {self._get_time_mode_accept_reason(item)}", 'success')
        else:
            self.log_message("  - None", 'warning')

        if rejected_items:
            self.log_message("", 'info')
            self.log_message("[REJECTED / SKIPPED]", 'error')

            for item in rejected_items:
                self.log_message(f"  - {item['video_source'].name}", 'error')
                self.log_message(f"    Mode: {self._format_time_mode_summary(item)}", 'error')
                self.log_message(
                    f"    Reason: {item.get('time_mode_reason') or 'Unsupported time-based mode.'}",
                    'error'
                )

        # ONLY show the unmatched section when unmatched files actually exist
        if orphan_360 or orphan_videos:
            self.log_message("", 'info')
            self.log_message("[UNMATCHED SOURCE FILES]", 'warning')

            for p in orphan_360:
                self.log_message(f"  - {p.name}", 'warning')
                self.log_message(
                    "    Reason: No matching .mp4/.mov found with the same base name.",
                    'warning'
                )

            for p in orphan_videos:
                self.log_message(f"  - {p.name}", 'warning')
                self.log_message(
                    "    Reason: No matching .360 found with the same base name.",
                    'warning'
                )
    
    def _parse_gpx_iso_datetime(self, value: str):
        """
        Parses GPX ISO timestamps such as:
            2026-04-19T09:28:11Z
            2026-04-19T09:28:11.000Z
        Returns a naive UTC datetime.
        """
        if not value:
            raise ValueError("Empty GPX time value.")

        text = value.strip()
        if text.endswith("Z"):
            text = text[:-1]

        for fmt in ("%Y-%m-%dT%H:%M:%S.%f", "%Y-%m-%dT%H:%M:%S"):
            try:
                return datetime.strptime(text, fmt)
            except ValueError:
                continue

        raise ValueError(f"Unsupported GPX timestamp format: {value}")


    def _format_gpx_iso_datetime(self, dt_obj: datetime):
        """
        Formats a datetime back to GPX style with millisecond precision and trailing Z.
        """
        return dt_obj.strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"


    def _get_video_duration_seconds(self, video_path: Path):
        """
        Returns the container duration in seconds via FFprobe.
        """
        cmd = [
            self.settings['FFprobePath'],
            "-v", "error",
            "-show_entries", "format=duration",
            "-of", "default=noprint_wrappers=1:nokey=1",
            str(video_path)
        ]

        rc, out = self.run_command(
            cmd,
            error_message=f"FFprobe duration read failed for {video_path}"
        )

        if rc != 0 or not out:
            return 0.0

        try:
            first_line = out.splitlines()[0].strip()
            return float(first_line)
        except Exception:
            return 0.0


    def _get_timewarp_gpx_work_dir(self) -> Path:
        """
        Returns the work directory for intermediate TimeWarp GPX files.
        """
        work_dir = Path(self.settings['TargetDir']) / TIMEWARP_SVS_GPX_DIR_NAME
        work_dir.mkdir(parents=True, exist_ok=True)
        return work_dir


    def _get_timewarp_intermediate_mov_path(self, item, custom_suffix: str) -> Path:
        """
        Returns the common-prep intermediate MOV that still contains the GPS/GPMF path
        used as GPX source for supported TimeWarp items.
        """
        stem = item["video_source"].stem
        return Path(self.settings['TargetDir']) / f"{stem}{custom_suffix}_gpmf_final.mov"


    def _rescale_gpx_track_to_video_duration(self, raw_gpx_path: Path, scaled_gpx_path: Path, target_duration_seconds: float):
        """
        Rescales GPX trackpoint timestamps so that the GPX duration exactly matches the
        actual TimeWarp video duration.

        This is the key step that makes supported TimeWarp videos SVS-compatible:
        - video duration stays short (TimeWarp output)
        - GPS timeline is compressed to the same duration
        """
        if target_duration_seconds <= 0:
            return False, "Target video duration is invalid or zero."

        if not raw_gpx_path.is_file():
            return False, f"Raw GPX file not found: {raw_gpx_path}"

        try:
            tree = ET.parse(raw_gpx_path)
            root = tree.getroot()

            trackpoint_times = []
            for trkpt in root.findall(f".//{{{GPX_NAMESPACE_URI}}}trkpt"):
                time_el = trkpt.find(GPX_TIME_TAG)
                if time_el is None or not (time_el.text or "").strip():
                    continue

                dt_obj = self._parse_gpx_iso_datetime(time_el.text)
                trackpoint_times.append((time_el, dt_obj))

            if len(trackpoint_times) < 2:
                return False, f"Not enough GPX trackpoints with timestamps in {raw_gpx_path.name}."

            source_start = trackpoint_times[0][1]
            source_end = trackpoint_times[-1][1]
            source_duration_seconds = (source_end - source_start).total_seconds()

            if source_duration_seconds <= 0:
                return False, f"Original GPX duration is invalid in {raw_gpx_path.name}."

            for time_el, old_dt in trackpoint_times:
                elapsed = (old_dt - source_start).total_seconds()
                ratio = elapsed / source_duration_seconds if source_duration_seconds > 0 else 0.0
                new_dt = source_start + timedelta(seconds=target_duration_seconds * ratio)
                time_el.text = self._format_gpx_iso_datetime(new_dt)

            metadata_time_el = root.find(f".//{{{GPX_NAMESPACE_URI}}}metadata/{{{GPX_NAMESPACE_URI}}}time")
            if metadata_time_el is not None:
                metadata_time_el.text = self._format_gpx_iso_datetime(source_start)

            tree.write(scaled_gpx_path, encoding="utf-8", xml_declaration=True)

            return True, (
                f"GPX timeline rescaled from {source_duration_seconds:.2f}s "
                f"to {target_duration_seconds:.2f}s."
            )

        except Exception as e:
            return False, f"GPX rescale failed for {raw_gpx_path.name}: {e}"
            
    def _sanitize_gpx_for_svs(self, gpx_path: Path, target_duration: float):
        """
        Normalizes GPX timestamps for SVS compatibility.

        Goals:
        - remove trackpoints without a valid time
        - keep only valid, parseable timestamps
        - enforce strictly increasing timestamps
        - redistribute timestamps linearly across the full target video duration

        This is mainly needed for Max 1 TimeWarp GPX output, where the raw GPX may
        contain empty or problematic timestamps that SVS rejects.
        """
        if not gpx_path.is_file():
            return False, f"GPX file not found: {gpx_path}"

        if target_duration <= 0:
            return False, "Target duration is invalid or zero."

        try:
            tree = ET.parse(gpx_path)
            root = tree.getroot()

            trkseg = root.find(f'.//{{{GPX_NAMESPACE_URI}}}trkseg')
            if trkseg is None:
                return False, "No GPX track segment found."

            valid_points = []

            for pt in trkseg.findall(f'{{{GPX_NAMESPACE_URI}}}trkpt'):
                time_el = pt.find(GPX_TIME_TAG)
                if time_el is None:
                    continue

                raw_text = time_el.text
                if raw_text is None:
                    continue

                raw_text = raw_text.strip()
                if not raw_text:
                    continue

                try:
                    parsed_dt = self._parse_gpx_iso_datetime(raw_text)
                except Exception:
                    continue

                valid_points.append((pt, time_el, parsed_dt))

            if len(valid_points) < 2:
                return False, "Not enough valid GPX points after sanitization."

            start_dt = valid_points[0][2]
            step_seconds = target_duration / (len(valid_points) - 1)

            sanitized_points = []
            for idx, (pt, time_el, _) in enumerate(valid_points):
                new_dt = start_dt + timedelta(seconds=(idx * step_seconds))
                time_el.text = self._format_gpx_iso_datetime(new_dt)
                sanitized_points.append(pt)

            trkseg.clear()
            for pt in sanitized_points:
                trkseg.append(pt)

            metadata_time_el = root.find(f'.//{{{GPX_NAMESPACE_URI}}}metadata/{{{GPX_NAMESPACE_URI}}}time')
            if metadata_time_el is not None:
                metadata_time_el.text = self._format_gpx_iso_datetime(start_dt)

            tree.write(gpx_path, encoding="utf-8", xml_declaration=True)

            return True, (
                f"GPX sanitized for SVS with {len(sanitized_points)} valid trackpoints "
                f"spread over {target_duration:.2f}s."
            )

        except Exception as e:
            return False, f"SVS GPX sanitization failed for {gpx_path.name}: {e}"

    def _get_timewarp_svs_gpx_source(self, item, custom_suffix):
        """
        Selects the correct raw GPX extraction source for supported TimeWarp items.

        Max 1:
            use the original .360 file directly (most reliable source of full GPS trackpoints)

        Max 2:
            keep the existing proven route and use the prepared *_gpmf_final.mov
        """
        family = item.get("family")
        prepared_mov = self._get_timewarp_intermediate_mov_path(item, custom_suffix)

        if family == "max1":
            original_360 = item.get("original_360")
            if not original_360:
                return None, prepared_mov, "missing original .360"
            return Path(original_360), prepared_mov, "original .360"

        return prepared_mov, prepared_mov, "prepared *_gpmf_final.mov"

    def _get_svs_fix_source_video_for_item(self, item, custom_suffix):
        """
        Returns the preferred source video for the final SVS fix step.

        Rules:
        - Max 1 + supported TimeWarp:
            use the clean converted source video directly (can be .mp4 or CineForm .mov)
        - Everything else:
            keep using the existing prepared *_gpmf_final.mov route
        """
        prepared_mov = self._get_timewarp_intermediate_mov_path(item, custom_suffix)

        raw_video_source = item.get("video_source")
        clean_source = Path(raw_video_source) if raw_video_source else None

        if item.get("family") == "max1" and item.get("time_mode") == "timewarp":
            if clean_source and clean_source.exists():
                return clean_source, "clean converted TimeWarp source"

            return prepared_mov, "fallback prepared *_gpmf_final.mov"

        return prepared_mov, "prepared *_gpmf_final.mov"

    def _prepare_timewarp_svs_gpxs(self, items, custom_suffix):
        """
        Prepares SVS-ready GPX files for supported TimeWarp items only.

        Family-aware behavior:
        - Max 1 TimeWarp:
            raw GPX is extracted from the original .360 file
            target duration is taken from the clean converted source video
        - Max 2 TimeWarp:
            raw GPX continues to use the existing proven *_gpmf_final.mov route
            target duration also continues to use that same prepared route

        In both cases:
        - the final GPX is written to SourceDir/<stem>.gpx so the existing SVS
          header-fix path can be reused with minimal impact on the old workflows
        """
        if not items:
            self.log_message("[TIMEWARP SVS] No supported TimeWarp items detected. No GPX rescaling needed.", 'info')
            return []

        work_dir = self._get_timewarp_gpx_work_dir()
        prepared_items = []

        self.log_message("", 'info')
        self.log_message("[TIMEWARP SVS] Preparing rescaled GPX files for supported TimeWarp items...", 'info')

        for item in items:
            gpx_source_path, _, source_label = self._get_timewarp_svs_gpx_source(item, custom_suffix)
            svs_fix_source_video, duration_source_label = self._get_svs_fix_source_video_for_item(item, custom_suffix)

            if gpx_source_path is None or not Path(gpx_source_path).exists():
                self.log_message(
                    f"  - [ERROR] Missing GPX source for {item['video_source'].name} ({source_label}).",
                    'error'
                )
                continue

            if not svs_fix_source_video.exists():
                self.log_message(
                    f"  - [ERROR] Missing duration source video for {item['video_source'].name} ({duration_source_label}).",
                    'error'
                )
                continue

            raw_gpx_path = work_dir / f"{item['video_source'].stem}_raw_original_timeline.gpx"
            final_gpx_path = Path(self.settings['SourceDir']) / f"{item['video_source'].stem}.gpx"

            self.log_message(
                f"  - [INFO] {item['video_source'].name}: extracting raw GPX from {source_label} ({Path(gpx_source_path).name})",
                'info'
            )

            extraction_cmd = [
                self.settings['ExifToolPath'],
                "-p", self.settings['GpxFormatPath'],
                "-ee",
                "-m",
                str(gpx_source_path)
            ]

            rc, out = self.run_command(
                extraction_cmd,
                error_message=f"TimeWarp GPX extraction failed for {Path(gpx_source_path).name}"
            )

            if rc != 0 or not out or "<trkpt" not in out:
                self.log_message(
                    f"  - [ERROR] No valid GPX content could be extracted for {Path(gpx_source_path).name}.",
                    'error'
                )
                continue

            try:
                raw_gpx_path.write_text(out, encoding="utf-8", newline="\n")
            except Exception as e:
                self.log_message(
                    f"  - [ERROR] Could not write raw GPX for {Path(gpx_source_path).name}: {e}",
                    'error'
                )
                continue

            target_duration = self._get_video_duration_seconds(svs_fix_source_video)
            ok, msg = self._rescale_gpx_track_to_video_duration(
                raw_gpx_path,
                final_gpx_path,
                target_duration
            )

            if not ok:
                self.log_message(
                    f"  - [ERROR] {item['video_source'].name}: {msg}",
                    'error'
                )
                continue

            # Extra SVS sanitization for Max 1 TimeWarp only
            if item.get("family") == "max1" and item.get("time_mode") == "timewarp":
                ok_svs, msg_svs = self._sanitize_gpx_for_svs(
                    final_gpx_path,
                    target_duration
                )

                if not ok_svs:
                    self.log_message(
                        f"  - [ERROR] {item['video_source'].name}: {msg_svs}",
                        'error'
                    )
                    continue

                self.log_message(
                    f"  - [INFO] {item['video_source'].name}: {msg_svs}",
                    'info'
                )

            self.log_message(
                f"  - [SUCCESS] {item['video_source'].name}: {msg}",
                'success'
            )
            self.log_message(
                f"    GPX ready for SVS fix: {final_gpx_path.name} (duration source: {svs_fix_source_video.name})",
                'info'
            )

            prepared_items.append(item)
        
        return prepared_items
    
    def _probe_video_stream_info(self, path):
        """
        Reads codec/resolution/fps/bitrate info from the first video stream.
        Independent of container (.mp4 / .mov).
        Returns a dict or None.
        Results are cached for the lifetime of the current workflow run.
        """
        cache_key = str(Path(path).resolve())
        cached = self._analysis_cache.get('ffprobe', {}).get(cache_key)
        if cached is not None:
            return dict(cached) if isinstance(cached, dict) else None

        cmd = [
            self.settings['FFprobePath'],
            "-v", "error",
            "-select_streams", "v:0",
            "-show_entries",
            "stream=codec_name,profile,pix_fmt,bits_per_raw_sample,width,height,avg_frame_rate,r_frame_rate,bit_rate",
            "-of", "json",
            str(path)
        ]

        rc, out = self.run_command(cmd, error_message=f"FFprobe failed for {path}")
        if rc != 0 or not out.strip():
            self._analysis_cache.setdefault('ffprobe', {})[cache_key] = None
            return None

        try:
            data = json.loads(out)
            streams = data.get("streams", [])
            if not streams:
                self._analysis_cache.setdefault('ffprobe', {})[cache_key] = None
                return None

            s = streams[0]

            def _fps(fr_str):
                if not fr_str or fr_str in ("0/0", "N/A"):
                    return None
                num, den = fr_str.split("/")
                num = float(num)
                den = float(den)
                return num / den if den else None

            info = {
                "path": str(path),
                "codec_name": (s.get("codec_name") or "").lower(),
                "profile": s.get("profile", ""),
                "pix_fmt": s.get("pix_fmt", ""),
                "bits_per_raw_sample": s.get("bits_per_raw_sample"),
                "width": int(s["width"]) if s.get("width") else None,
                "height": int(s["height"]) if s.get("height") else None,
                "bit_rate": int(s["bit_rate"]) if s.get("bit_rate") and str(s.get("bit_rate")).isdigit() else None,
                "fps": _fps(s.get("avg_frame_rate") or s.get("r_frame_rate")),
            }

            self._analysis_cache.setdefault('ffprobe', {})[cache_key] = dict(info)
            return info

        except Exception as e:
            self.log_message(f"[WARNING] Could not parse FFprobe JSON for {Path(path).name}: {e}", 'warning')
            self._analysis_cache.setdefault('ffprobe', {})[cache_key] = None
            return None
            
    def _classify_video_codec(self, info):
        """
        Normalizes codec names to: hevc / cineform / h264 / unknown
        """
        if not info:
            return "unknown"

        codec = (info.get("codec_name") or "").lower()

        if codec == "hevc":
            return "hevc"
        if codec == "cfhd":
            return "cineform"
        if codec == "h264":
            return "h264"

        return codec or "unknown"

    def _get_quality_for_source_codec(self, codec_name):
        """
        Returns (cpu_crf, gpu_qp, label) based on the detected source codec.
        """
        if codec_name == "cineform":
            return (
                self.settings.get('CineformCRF', 15),
                self.settings.get('CineformQP', 16),
                "CineForm"
            )

        return (
            self.settings.get('NadirCRF', 17),
            self.settings.get('NadirQP', 18),
            "Standard"
        )
        
    def benchmark_encode(
        self,
        ffmpeg_cmd,
        encoder_name,
        source_codec,
        quality_value,
        quality_type,
        input_video_path,
        label="ENCODE"
    ):
        """
        Runs an FFmpeg encode command and logs benchmark information.
        Returns True on success, False on failure.
        """

        # --- Determine resolution (best effort) ---
        try:
            w, h = self._get_video_dims(input_video_path)
            resolution = f"{w}x{h}" if w and h else "unknown"
        except Exception:
            resolution = "unknown"

        # --- Run benchmark ---
        start_time = time.time()
        rc, _ = self.run_command(ffmpeg_cmd)
        elapsed = time.time() - start_time

        # --- Estimate FPS (best effort) ---
        fps_est = "n/a"
        try:
            info = self._probe_video_stream_info(input_video_path)
            if info and info.get("fps"):
                fps_est = round((info["fps"] * elapsed) / elapsed, 2)
        except Exception:
            pass

        if rc == 0:
            self.log_message(
                f"[BENCH] {label} | Encoder={encoder_name} | Source={source_codec} | "
                f"{quality_type}={quality_value} | Res={resolution} | "
                f"Time={elapsed:.1f}s | FPS~{fps_est}",
                "info"
            )
            return True
        else:
            self.log_message(
                f"[BENCH] {label} FAILED | Encoder={encoder_name} | Source={source_codec} | "
                f"{quality_type}={quality_value} | Time={elapsed:.1f}s",
                "error"
            )
            return False

    def update_flags_from_ui(self):
        """Maps UI selections to internal workflow flags."""
        choice = self.workflow_choice.get()
        mapillary_action = self.mapillary_actions_var.get()

        # Global workflow channels only.
        # Actual Max 1 / Max 2 routing will be determined per matched source item.
        self.settings['RunCorePrep'] = (choice in [1, 2, 3])
        self.settings['RunGPX'] = (choice in [2, 3])
        self.settings['RunSVSHeaderFix'] = (choice in [2, 3])

        if choice in [1, 3]:
            self.settings['RunSample'] = (mapillary_action in [1, 2])
            self.settings['RunProcess'] = (mapillary_action in [1, 2])
            self.settings['RunUpload'] = (mapillary_action == 1)
        else:
            self.settings['RunSample'] = False
            self.settings['RunProcess'] = False
            self.settings['RunUpload'] = False

        self.settings['RunNadirPatch'] = self.run_nadir_patch_var.get()

        # Informational only: Max family is now auto-detected from .360 metadata.
        self.settings['CameraModel'] = 'AUTO'

    def log_mapillary_account_help(self):
        """
        Logs clear guidance when Mapillary upload fails due to missing/invalid account/profile.
        """
        self.log_message("[INFO] Mapillary upload could not be completed with the configured profile.", 'warning')
        self.log_message("[INFO] Please create or activate your account first via: www.mapillary.com", 'warning')
        self.log_message("[INFO] After that, enter the correct Mapillary Profile Name in Configuration and try Upload again.", 'warning')

    def _is_benign_exiftool_warning(self, tool_name, line):
        """
        Returns True only for known harmless ExifTool warning lines
        that we do not want to show in the normal log output.
        """
        if not tool_name:
            return False

        tool_name = str(tool_name).lower()
        if "exiftool" not in tool_name:
            return False

        line_norm = str(line).strip()

        benign_patterns = [
            "Warning: [minor] The ExtractEmbedded option may find more tags in the media data",
            "Warning: No writable tags set"
        ]

        return any(p in line_norm for p in benign_patterns)

    def _parse_size_token_to_bytes(self, token):
        """
        Converts tqdm-style size tokens like:
        2.43G, 950M, 31.0MB, 512K
        into bytes.

        Decimal units are used intentionally to match upload/network reporting.
        """
        if not token:
            return None

        token = str(token).strip().upper()
        token = token.replace("/S", "")
        token = token.replace("IB", "B")

        match = re.match(r"^([0-9]*\.?[0-9]+)\s*([KMGTPE]?)(B)?$", token)
        if not match:
            return None

        value = float(match.group(1))
        unit = match.group(2)

        multipliers = {
            "": 1,
            "K": 1_000,
            "M": 1_000_000,
            "G": 1_000_000_000,
            "T": 1_000_000_000_000,
            "P": 1_000_000_000_000_000,
            "E": 1_000_000_000_000_000_000,
        }

        return int(value * multipliers.get(unit, 1))


    def _parse_elapsed_token_to_seconds(self, token):
        """
        Converts elapsed time tokens like:
        01:25      -> 85 seconds
        1:02:15    -> 3735 seconds
        """
        if not token:
            return None

        token = str(token).strip()
        parts = token.split(":")

        try:
            parts = [int(p) for p in parts]
        except ValueError:
            return None

        if len(parts) == 2:
            minutes, seconds = parts
            return minutes * 60 + seconds

        if len(parts) == 3:
            hours, minutes, seconds = parts
            return hours * 3600 + minutes * 60 + seconds

        return None


    def _format_upload_size(self, num_bytes):
        """
        Formats bytes for user-facing upload logging.
        """
        if num_bytes is None:
            return None

        if num_bytes >= 1_000_000_000:
            return f"{num_bytes / 1_000_000_000:.2f} GB"
        if num_bytes >= 1_000_000:
            return f"{num_bytes / 1_000_000:.1f} MB"
        if num_bytes >= 1_000:
            return f"{num_bytes / 1_000:.1f} KB"
        return f"{num_bytes} B"


    def _format_upload_duration(self, seconds):
        """
        Formats duration as:
        MM:SS
        or
        HH:MM:SS
        """
        if seconds is None:
            return None

        seconds = max(int(round(seconds)), 0)
        hours, remainder = divmod(seconds, 3600)
        minutes, secs = divmod(remainder, 60)

        if hours:
            return f"{hours:02d}:{minutes:02d}:{secs:02d}"
        return f"{minutes:02d}:{secs:02d}"


    def _format_average_upload_speed(self, num_bytes, seconds):
        """
        Returns average upload speed in Mbit/s.
        """
        if not num_bytes or not seconds:
            return None

        seconds = float(seconds)
        if seconds <= 0:
            return None

        mbit_per_sec = (num_bytes * 8) / seconds / 1_000_000
        return f"{mbit_per_sec:.1f} Mbit/s"


    def _log_completed_mapillary_sequence(self, stats):
        """
        Logs a summary line, for example:
        [INFO] Uploading of sequence 1 completed (2.43 GB / 01:25 / 228.7 Mbit/s)
        """
        if not stats:
            return

        seq_num = stats.get("seq_num")
        total_bytes = stats.get("total_bytes") or stats.get("transferred_bytes")
        elapsed_seconds = stats.get("elapsed_seconds")

        details = []

        size_text = self._format_upload_size(total_bytes)
        duration_text = self._format_upload_duration(elapsed_seconds)
        speed_text = self._format_average_upload_speed(total_bytes, elapsed_seconds)

        if size_text:
            details.append(size_text)
        if duration_text:
            details.append(duration_text)
        if speed_text:
            details.append(speed_text)

        if details:
            self.log_message(
                f" [INFO] Uploading of sequence {seq_num} completed ({' / '.join(details)})",
                "info"
            )
        else:
            self.log_message(
                f" [INFO] Uploading of sequence {seq_num} completed.",
                "info"
            )

    def run_command(self, command, cwd=None, error_message="Error executing command", priority_class=None):
        """
        Executes an external command, logs FULL output to Extended Log,
        and returns (returncode, stdout_text) for internal processing.

        priority_class (Windows only):
          - If provided: runs the process with CREATE_NO_WINDOW | priority_class
          - If not provided: applies the configured FFmpeg priority (below normal by default)
        """

        # Create string representation for the log
        cmd_str = " ".join([str(x) for x in command])
        tool_name = os.path.basename(str(command[0])) if command and len(command) > 0 else "unknown"
        tool_name_lower = tool_name.lower()
        command_lower = [str(x).lower() for x in command]

        is_mapillary_upload = (
            "mapillary_tools" in tool_name_lower and
            any(arg == "upload" for arg in command_lower)
        )

        current_upload_stats = None
        last_upload_seq = None
        last_upload_total = None

        # Detect NADIR worker slot (set in _nadir_job via thread-local storage)
        slot = getattr(self._tls, "nadir_slot", None)
        proc_prefix = f"[P{slot}] " if slot else ""
        proc_tag = f"nadir_p{slot}" if slot else None

        # Log command to extended log (colored per nadir worker if applicable)
        if proc_tag:
            self.log_message(f"{proc_prefix}EXECUTING: {cmd_str}", proc_tag, extended_only=True)
        else:
            self.log_message(f"EXECUTING: {cmd_str}", "cmd", extended_only=True)

        collected_output = []

        # --- Build Windows creation flags (priority injection + FFmpeg default policy) ---
        popen_kwargs = {}
        if os.name == "nt":
            # If an explicit priority_class is supplied, use ONLY that class
            # (do NOT OR with other priority classes).
            if priority_class is not None:
                creation_flags = CREATE_NO_WINDOW | priority_class
            else:
                creation_flags = CREATE_NO_WINDOW

                # Default: FFmpeg on BelowNormal so the PC remains responsive
                if tool_name.lower() == "ffmpeg.exe":
                    pr = (self.settings.get("FFmpegPriority", "belownormal") or "belownormal").lower()
                    if pr == "idle":
                        creation_flags |= subprocess.IDLE_PRIORITY_CLASS
                    else:
                        creation_flags |= subprocess.BELOW_NORMAL_PRIORITY_CLASS

            popen_kwargs["creationflags"] = creation_flags

        try:
            process = subprocess.Popen(
                command,
                cwd=cwd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                stdin=subprocess.DEVNULL,
                text=True,
                encoding="utf-8",
                errors="replace",
                shell=False,
                **popen_kwargs
            )

            # Read output line by line
            benign_exiftool_warnings = 0

            upload_seq_pattern = re.compile(
                r"Uploading\s+\w+\s+\((\d+)/(\d+)\):"
            )
            upload_bytes_pattern = re.compile(
                r"\|\s*([0-9]*\.?[0-9]+[KMGTP]?B?)/([0-9]*\.?[0-9]+[KMGTP]?B?)\s+\["
            )

            upload_elapsed_pattern = re.compile(
                r"\[([0-9:]+)<"
            )

            for line in process.stdout:
                clean_line = line.rstrip()
                if not clean_line:
                    continue

                # Suppress only known harmless ExifTool warnings
                if self._is_benign_exiftool_warning(tool_name, clean_line):
                    benign_exiftool_warnings += 1
                    collected_output.append(clean_line)   # keep in returned output for safety
                    continue

                if proc_tag:
                    self.log_message(f"{proc_prefix}  [{tool_name}] {clean_line}", proc_tag, extended_only=True)
                else:
                    self.log_message(f"  [{tool_name}] {clean_line}", "info", extended_only=True)

                collected_output.append(clean_line)
                if is_mapillary_upload:
                    seq_match = upload_seq_pattern.search(clean_line)

                    if seq_match:
                        seq_num = int(seq_match.group(1))
                        seq_total = int(seq_match.group(2))

                        # Sequence changed -> close previous one and start the new one
                        if current_upload_stats is None or seq_num != last_upload_seq:
                            if current_upload_stats is not None:
                                self._log_completed_mapillary_sequence(current_upload_stats)

                            self.log_message(
                                f" [INFO] Uploading sequence {seq_num} of {seq_total}...",
                                "info"
                            )

                            current_upload_stats = {
                                "seq_num": seq_num,
                                "seq_total": seq_total,
                                "transferred_bytes": None,
                                "total_bytes": None,
                                "elapsed_seconds": None,
                            }

                            last_upload_seq = seq_num
                            last_upload_total = seq_total

                        bytes_matches = upload_bytes_pattern.findall(clean_line)
                        if bytes_matches and current_upload_stats is not None:
                            transferred_token, total_token = bytes_matches[-1]
                            current_upload_stats["transferred_bytes"] = self._parse_size_token_to_bytes(transferred_token)
                            current_upload_stats["total_bytes"] = self._parse_size_token_to_bytes(total_token)


                        elapsed_match = upload_elapsed_pattern.search(clean_line)
                        if elapsed_match and current_upload_stats is not None:
                            current_upload_stats["elapsed_seconds"] = self._parse_elapsed_token_to_seconds(elapsed_match.group(1))

            process.wait()
            if benign_exiftool_warnings:
                self.log_message(
                    f"  [{tool_name}] {benign_exiftool_warnings} known harmless ExifTool warnings suppressed.",
                    "info",
                    extended_only=True
                )

            return_code = process.returncode

        except FileNotFoundError:
            msg = f"Command not found: {command[0]}"
            self.log_message(f"    [FATAL ERROR] {msg}", "error")
            return 1, msg

        except Exception as e:
            self.log_message(f"    [FATAL ERROR] {error_message}: {e}", "error")
            return 1, str(e)

        # Build output text for the caller
        full_output = "\n".join(collected_output)

        # Log result to extended log
        if return_code == 0:
            if is_mapillary_upload and current_upload_stats is not None:
                self._log_completed_mapillary_sequence(current_upload_stats)

                if last_upload_total and current_upload_stats.get("seq_num") == last_upload_total:
                    self.log_message(
                        f" [SUCCESS] All {last_upload_total} upload sequences completed.",
                        "success"
                    )

            if proc_tag:
                self.log_message(f"{proc_prefix}FINISHED: {tool_name}", proc_tag, extended_only=True)
            else:
                self.log_message(f"FINISHED: {tool_name}", "success", extended_only=True)

        else:
            if proc_tag:
                self.log_message(f"{proc_prefix}FAILED: {tool_name} (Code {return_code})", proc_tag, extended_only=True)
            else:
                self.log_message(f"FAILED: {tool_name} (Code {return_code})", "error", extended_only=True)

            if is_mapillary_upload and current_upload_stats is not None:
                seq_num = current_upload_stats.get("seq_num")
                seq_total = current_upload_stats.get("seq_total")

                self.log_message(
                    f" [WARNING] Upload stopped during sequence {seq_num}"
                    + (f" of {seq_total}." if seq_total else "."),
                    "warning"
                )

            # Also show a small error in the MAIN log so the user knows something went wrong
            self.log_message(f"    [COMMAND FAILED] {tool_name} (Code {return_code})", "error")

        return return_code, full_output

    def _phase1_extract_gpmf(self, step_counter, items):
        """
        Phase 1 - Step 1:
        Extracts the GPMF metadata track from all .360 files in the source directory.
        Returns the updated step_counter.
        """
        step_counter += 1
        self.check_for_abort("GPMF Extraction")
        self.log_message(f"\n[STEP {step_counter}/10] Extracting GPMF metadata...", 'info')

        original_files = [item["original_360"] for item in items]
        total_files = len(original_files)

        self.settings['TotalVideosProcessed'] = total_files
        self.update_progress(0, total_files)

        if total_files == 0:
            self.log_message(" [ERROR] No matching .360 + .mp4/.mov pairs found. Core Prep aborted.", 'error')
            self.settings['RunCorePrep'] = False
            return step_counter

        for i, file in enumerate(original_files, 1):
            self.check_for_abort("GPMF Extraction loop")
            self.update_progress(i, total_files)
            self.log_message(f" -> Processing file {i}/{total_files}: {file.name}", 'info')

            gpmf_output_path = Path(self.settings['SourceDir']) / f"{file.stem}_gpmf.mov"
            command = [
                self.settings['FFmpegPath'],
                "-i", str(file),
                "-map", "0:3",
                "-c", "copy",
                str(gpmf_output_path),
                "-y"
            ]

            if self.run_command(command, error_message=f"FFmpeg GPMF extraction failed for {file.name}")[0] == 0:
                self.log_message(" [SUCCESS] GPMF track extracted.", 'success')

        return step_counter
    
    def _get_nadir_cache_dir(self) -> Path:
        """
        Returns the cache directory for nadir patch assets and ensures it exists.
        Cache is stored inside TargetDir/nadir_cache.
        """
        cache_dir = Path(self.settings['TargetDir']) / "nadir_cache"
        cache_dir.mkdir(parents=True, exist_ok=True)
        return cache_dir
    
    def _hash_file_sha256(self, file_path: Path, chunk_size: int = 4 * 1024 * 1024) -> str:
        """
        Returns SHA-256 hash (hex) of a file.
        Uses chunked reads for reliability and memory efficiency.
        """
        h = hashlib.sha256()
        with open(file_path, "rb") as f:
            while True:
                chunk = f.read(chunk_size)
                if not chunk:
                    break
                h.update(chunk)
        return h.hexdigest()
        
    def _safe_cache_token(self) -> str:
        """
        Unique token for temporary files (parallel safe).
        """
        return f"{os.getpid()}_{threading.get_ident()}_{int(time.time() * 1000)}"
    
    def _get_or_create_scaled_nadir_patch(self, w: int, h: int):
        """
        Creates (if needed) and returns a cached, pre-scaled nadir patch PNG.

        Returns:
            (scaled_patch_path: Path, nadir_h: int, y_pos: int)

        Cache design (reliability first):
          - base patch: depends ONLY on the nadir source image content (SHA-256 hash)
          - scaled patch: depends on (base_hash + scale_factor + w + nadir_h)

        Parallel-safe:
          - lock to prevent concurrent writers
          - unique temporary filenames
          - atomic replace into final cache filenames
        """

        # --- Basic validation ---
        src_img = Path(self.settings.get('NadirImagePath', '') or '')
        if not src_img.is_file():
            raise FileNotFoundError(f"Nadir image not found: {src_img}")

        sf = float(self.settings.get('NadirScaleFactor', 0.2500))

        # Compute nadir height and y position (same as your existing logic)
        nadir_h = int(math.trunc(h * sf))
        if nadir_h % 2 != 0:
            nadir_h += 1
        y_pos = h - nadir_h

        cache_dir = self._get_nadir_cache_dir()

        # --- Compute stable base hash from file content (reliability > speed) ---
        base_hash = self._hash_file_sha256(src_img)  # full SHA-256 hex

        # Base patch key: only depends on the source image content
        base_patch = cache_dir / f"base_patch_{base_hash}.png"

        # Scaled patch key: depends on base hash + scale factor + dimensions
        scaled_key_str = f"{base_hash}|sf={sf:.6f}|w={w}|nh={nadir_h}"
        scaled_key_hash = hashlib.sha1(scaled_key_str.encode("utf-8", errors="ignore")).hexdigest()[:16]
        scaled_patch = cache_dir / f"scaled_patch_{scaled_key_hash}_{w}x{nadir_h}.png"

        token = self._safe_cache_token()

        with self.nadir_cache_lock:

            # ------------------------------------------------------------
            # 1) Create base patch (ImageMagick DePolar pipeline) if needed
            # ------------------------------------------------------------
            if not base_patch.exists():

                mgk = self.settings.get('ImageMagickPath', '')
                if not mgk or not Path(mgk).is_file():
                    raise FileNotFoundError(f"ImageMagick not found at: {mgk}")

                # Temp files (unique)
                t1 = cache_dir / f"t1_{token}.png"
                t2 = cache_dir / f"t2_{token}.png"
                t3 = cache_dir / f"t3_{token}.png"
                tmp_base = cache_dir / f"base_{token}.png"

                cmds = [
                    [mgk, str(src_img), "-rotate", "180", "-strip", str(t1)],
                    [mgk, str(t1), "-distort", "DePolar", "0", str(t2)],
                    [mgk, str(t2), "-flip", str(t3)],
                    [mgk, str(t3), "-flop", str(tmp_base)]
                ]

                success = True
                for c in cmds:
                    if self.run_command(c)[0] != 0:
                        success = False
                        break

                # Cleanup intermediate temps
                for p in (t1, t2, t3):
                    try:
                        if p.exists():
                            p.unlink()
                    except:
                        pass

                if not success or not tmp_base.exists():
                    try:
                        if tmp_base.exists():
                            tmp_base.unlink()
                    except:
                        pass
                    raise RuntimeError("Failed to generate base nadir patch with ImageMagick.")

                # Atomic replace into cache
                try:
                    if base_patch.exists():
                        base_patch.unlink()
                except:
                    pass
                tmp_base.replace(base_patch)

            # ------------------------------------------------------------
            # 2) Create scaled patch (FFmpeg scale) if needed
            # ------------------------------------------------------------
            if not scaled_patch.exists():

                ffmpeg = self.settings.get('FFmpegPath', '')
                if not ffmpeg or not Path(ffmpeg).is_file():
                    raise FileNotFoundError(f"FFmpeg not found at: {ffmpeg}")

                tmp_scaled = cache_dir / f"scaled_{token}.png"

                # Use FFmpeg scaling to match previous behavior (but done once)
                cmd_scale = [
                    ffmpeg, "-y",
                    "-i", str(base_patch),
                    "-vf", f"scale={w}:{nadir_h}",
                    "-frames:v", "1",
                    "-f", "image2",
                    "-update", "1",
                    str(tmp_scaled)
                ]

                if self.run_command(cmd_scale)[0] != 0 or not tmp_scaled.exists():
                    try:
                        if tmp_scaled.exists():
                            tmp_scaled.unlink()
                    except:
                        pass
                    raise RuntimeError("Failed to generate scaled nadir patch with FFmpeg.")

                # Atomic replace into cache
                try:
                    if scaled_patch.exists():
                        scaled_patch.unlink()
                except:
                    pass
                tmp_scaled.replace(scaled_patch)

        return scaled_patch, nadir_h, y_pos
    
    def _phase1_mux_video_and_gpmf(self, step_counter, custom_suffix, nadir_work, items):
        """
        Phase 1 - Step 2:
        Muxes the source MP4 video with the extracted GPMF track.
        Optionally applies a Nadir patch first.

        UPDATED:
        - Nadir patch assets are cached and pre-scaled (no per-frame scale in FFmpeg filter).
        - Nadir encode step can run in parallel (config: ParallelNadirJobs), but mux remains sequential.
        """
        step_counter += 1
        self.check_for_abort("Muxing Video")
        self.log_message(f"\n[STEP {step_counter}/10] {STEP_LABEL_MUX}...", 'info')

        video_source_files = [item["video_source"] for item in items]
        total_files = len(video_source_files)
        file_number_map = {f: i for i, f in enumerate(video_source_files, 1)}
        item_by_source = {item["video_source"]: item for item in items}
        self.update_progress(0, total_files)

        # Ensure nadir_work exists (stores per-file nadir_temp.mp4 only)
        try:
            nadir_work.mkdir(parents=True, exist_ok=True)
        except:
            pass

        # Map: original file Path -> nadir temp mp4 Path
        nadir_temp_map = {}

        if self.settings['RunCorePrep']:

            # ---------------------------------------------------------------------
            # A) PARALLEL NADIR ENCODE PRE-PASS (only this part is parallel)
            # ---------------------------------------------------------------------
            if self.settings.get('RunNadirPatch', False) and total_files > 0:
                jobs = 1
                try:
                    jobs = int(self.settings.get('ParallelNadirJobs', 1))
                except:
                    jobs = 1
                if jobs < 1:
                    jobs = 1

                # --- SANITY CHECK: parallel CPU (libx265) encodes can make the PC unresponsive ---
                if jobs > 1 and not self.settings.get('UseGPUEncoding', False):
                    self.log_message(
                        " [WARNING] ParallelNadirJobs > 1 while 'Enable GPU Encoding' is OFF. "
                        "This will run multiple CPU (libx265) encodes at the same time and may heavily load the system "
                        "(reduced responsiveness / slower UI). "
                        "Recommendation: enable GPU encoding or set ParallelNadirJobs=1 for older/slower systems.",
                        'warning'
                    )

                    # Extra sanity option: auto-limit to 1 job when GPU encoding is disabled
                    jobs = 1
                    self.log_message(
                        " [INFO] Auto-safety enabled: ParallelNadirJobs has been reduced to 1 because GPU encoding is disabled.",
                        'info'
                    )

                # Process slot pool (P1..P4). Each running worker takes one slot.
                slot_pool = queue.Queue()
                for s in range(1, jobs + 1):
                    slot_pool.put(s)
                
                def _nadir_job(file_path: Path):
                    """
                    Worker: build nadir_temp.mp4 for one file.
                    Returns: (file_path, nadir_temp_path or None)
                    """
                    slot = slot_pool.get()
                    self._tls.nadir_slot = slot
                    proc_tag = f"nadir_p{slot}"
                    proc_prefix = f"[P{slot}] "

                    try:
                        self.check_for_abort("Nadir pre-encode worker")

                        file_no = file_number_map.get(file_path)
                        if file_no is not None:
                            self.log_message(
                                f" [NADIR] {proc_prefix}Processing file {file_no}/{total_files}: {file_path.name}",
                                proc_tag
                            )

                        source_info = self._probe_video_stream_info(file_path)
                        source_codec = self._classify_video_codec(source_info)
                        source_crf, source_qp, source_label = self._get_quality_for_source_codec(source_codec)

                        # dims and bit depth (existing behavior)
                        w, h = self._get_video_dims(file_path)
                        if not w or not h:
                            self.log_message(
                                f" [NADIR] {proc_prefix}Could not determine dimensions for {file_path.name}. Skipping.",
                                'error'
                            )
                            return (file_path, None)

                        bit_depth = self._get_video_bit_depth(file_path)

                        # Output pix fmt (keep exactly as your current behavior: 420 8/10/12-bit)
                        if bit_depth == 12:
                            pix_fmt = "yuv420p12le"
                        elif bit_depth == 10:
                            pix_fmt = "yuv420p10le"
                        else:
                            pix_fmt = "yuv420p"

                        # Get cached + pre-scaled patch and overlay position
                        # This helper must exist (from step 6.2)
                        scaled_patch, nadir_h, y_pos = self._get_or_create_scaled_nadir_patch(w, h)

                        # Determine FPS dynamically to avoid timestamp/PTS discontinuities causing inflated ffmpeg 'time='
                        fps = self._get_video_fps(file_path)
                        if not fps:
                            fps = 25.0
                            self.log_message(
                                f" [NADIR] {proc_prefix}{file_path.name} -> FPS unknown, fallback to 25.0",
                                proc_tag
                            )

                        self.log_message(
                            f" [NADIR] {proc_prefix}{file_path.name} -> detected FPS={fps:.3f}",
                            proc_tag
                        )

                        # Filter: NO per-frame patch scaling anymore (patch already scaled)
                        vf = f"[0:v]setpts=N/({fps}*TB)[v0];[v0][1:v]overlay=0:{y_pos}:shortest=1,format={pix_fmt}[final_out]"

                        # Output temp file
                        nadir_vid = nadir_work / f"{file_path.stem}_nadir_temp.mp4"

                        # Encoder selection (keep your existing logic)
                        encoder_name = ""
                        hwaccel_args = []
                        encoder_args = []

                        if self.settings.get('UseGPUEncoding', False):
                            encoder_choice = self.settings.get('GPUEncoder', 'auto').split(' ')[0]
                            if encoder_choice in ['nvenc', 'auto']:
                                encoder_name = "hevc_nvenc"
                                hwaccel_args = ["-hwaccel", "cuda"]
                            elif encoder_choice == 'qsv':
                                encoder_name = "hevc_qsv"
                                hwaccel_args = ["-hwaccel", "qsv"]
                            elif encoder_choice == 'amf':
                                encoder_name = "hevc_amf"
                                hwaccel_args = []
                            else:
                                encoder_name = "hevc_nvenc"
                                hwaccel_args = ["-hwaccel", "cuda"]

                            qp_val = source_qp
                            encoder_args = [
                                "-c:v", encoder_name,
                                "-preset", "p7",
                                "-rc", "constqp",
                                "-spatial-aq", "1",
                                "-temporal-aq", "1",
                                "-aq-strength", "8",
                                "-qp", str(qp_val),
                                "-tag:v", "hvc1",
                                "-c:a", "copy"
                            ]
                            used_quality = qp_val
                            quality_type = "QP"
                        else:
                            encoder_name = "libx265"
                            encoder_args = [
                                "-c:v", encoder_name,
                                "-preset", "slow",
                                "-x265-params",
                                "aq-mode=3:aq-strength=1.0:psy-rd=2.0:psy-rdoq=2.0:deblock=-1,-1",
                                "-crf", str(source_crf),
                                "-tag:v", "hvc1",
                                "-c:a", "copy"
                            ]
                            used_quality = source_crf
                            quality_type = "CRF"

                        # Build command
                        c_ov = [self.settings['FFmpegPath'], "-y"] + hwaccel_args + [
                            "-i", str(file_path),
                            "-loop", "1", "-i", str(scaled_patch),
                            "-filter_complex", vf,
                            "-map", "[final_out]",
                            "-map", "0:a:0?"
                        ] + encoder_args + ["-shortest", str(nadir_vid)]

                        self.log_message(
                            f" [NADIR] {proc_prefix}{file_path.name} -> encoder={encoder_name}, quality={used_quality} ({quality_type}), pix_fmt={pix_fmt}",
                            proc_tag
                        )

                        success = self.benchmark_encode(
                            ffmpeg_cmd=c_ov,
                            encoder_name=encoder_name,
                            source_codec=source_codec,
                            quality_value=used_quality,
                            quality_type=quality_type,
                            input_video_path=file_path,
                            label="NADIR"
                        )

                        if success:
                            return (file_path, nadir_vid)
                        else:
                            self.log_message(f" [NADIR] {proc_prefix}Encode failed for {file_path.name}.", 'error')
                            return (file_path, None)

                    except UserAbortException:
                        return (file_path, None)
                    except Exception as e:
                        self.log_message(f" [NADIR] {proc_prefix}Unexpected error for {file_path.name}: {e}", 'error')
                        return (file_path, None)
                    
                    finally:
                        # Clear thread-local context and return the slot to the pool
                        try:
                            del self._tls.nadir_slot
                        except:
                            pass
                        slot_pool.put(slot)

                # Run jobs (parallel if jobs>1, otherwise sequential)
                if jobs > 1:
                    from concurrent.futures import ThreadPoolExecutor, as_completed
                    futures = []
                    with ThreadPoolExecutor(max_workers=jobs) as ex:
                        for f in video_source_files:
                            futures.append(ex.submit(_nadir_job, f))

                        for fut in as_completed(futures):
                            self.check_for_abort("Nadir pre-encode join")
                            src_file, out_path = fut.result()
                            if out_path:
                                nadir_temp_map[src_file] = out_path
                else:
                    for f in video_source_files:
                        self.check_for_abort("Nadir pre-encode loop")
                        src_file, out_path = _nadir_job(f)
                        if out_path:
                            nadir_temp_map[src_file] = out_path

                self.log_message(f" [NADIR] Pre-encode done. Success: {len(nadir_temp_map)}/{total_files}", 'success')

            # ---------------------------------------------------------------------
            # B) SEQUENTIAL MUX (unchanged logic, but uses nadir_temp_map if present)
            # ---------------------------------------------------------------------
            for i, file in enumerate(video_source_files, 1):
                self.check_for_abort("Muxing Video loop")
                self.update_progress(i, total_files)
                self.log_message(f" -> Processing file {i}/{total_files}: {file.name}", 'info')

                current_item = item_by_source.get(file)
                if current_item and current_item.get("time_mode") == "timewarp":
                    self.log_message(
                        f" [INFO] TimeWarp source confirmed for {file.name}: "
                        f"TimeWarp {current_item['timewarp_rate']}X "
                        f"(Rate={current_item.get('time_mode_raw_rate')}, "
                        f"Video FPS={current_item.get('time_mode_output_fps'):.2f}, "
                        f"Effective FPS={current_item.get('time_mode_effective_unique_fps'):.2f})",
                        'info'
                    )

                source_info = self._probe_video_stream_info(file)
                source_codec = self._classify_video_codec(source_info)
                source_crf, source_qp, source_label = self._get_quality_for_source_codec(source_codec)

                self.log_message(
                    f" [SOURCE] Detected codec: {source_codec} | Quality profile: {source_label} "
                    f"(CRF={source_crf}, QP={source_qp})",
                    'info'
                )

                gpmf_source_path = Path(self.settings['SourceDir']) / f"{file.stem}_gpmf.mov"
                intermediate_base_name = f"{file.stem}{custom_suffix}"
                intermediate_file_name = f"{intermediate_base_name}_gpmf_final.mov"
                final_output_path = Path(self.settings['TargetDir']) / intermediate_file_name

                input_video_mux = file
                is_nadir = False

                if self.settings.get('RunNadirPatch', False):
                    if file in nadir_temp_map:
                        input_video_mux = nadir_temp_map[file]
                        is_nadir = True
                        self.log_message(f" [NADIR] Using pre-encoded file: {input_video_mux.name}", 'info')
                    else:
                        self.log_message(f" [NADIR] No pre-encoded nadir file for {file.name}. Using source.", 'warning')

                # Existing mux command logic
                if is_nadir:
                    cmd = [
                        self.settings['FFmpegPath'],
                        "-i", str(input_video_mux),
                        "-i", str(gpmf_source_path),
                        "-map", "0",
                        "-map", "1",
                        "-c", "copy",
                        str(final_output_path),
                        "-y"
                    ]
                else:
                    cmd = [
                        self.settings['FFmpegPath'],
                        "-i", str(file),
                        "-i", str(gpmf_source_path),
                        "-map", "0",
                        "-map", "-0:3",
                        "-map", "1",
                        "-c", "copy",
                        str(final_output_path),
                        "-y"
                    ]

                if self.run_command(cmd)[0] == 0:
                    self.log_message(f" [SUCCESS] Muxed to {final_output_path.name}.", 'success')
                    try:
                        os.remove(gpmf_source_path)
                    except:
                        pass

        # Clean up only nadir_work temp area (do NOT delete cache dir)
        if nadir_work.exists():
            shutil.rmtree(nadir_work, ignore_errors=True)

        return step_counter 
    
    def _phase1_transfer_metadata(self, step_counter, custom_suffix, items):
        """
        Phase 1 - Step 3:
        Transfers metadata from the original .360 files to the generated *_gpmf_final.mov files.
        Returns the updated step_counter.
        """
        step_counter += 1
        self.check_for_abort("Metadata Correction")
        self.log_message(f"\n[STEP {step_counter}/10] Transferring metadata...", 'info')

        intermediate_mov_files = list(Path(self.settings['TargetDir']).glob("*_gpmf_final.mov"))
        intermediate_mov_files = self._filter_intermediate_mov_files(
            intermediate_mov_files,
            items,
            custom_suffix=custom_suffix
        )
        total_files = len(intermediate_mov_files)
        self.update_progress(0, total_files)

        if total_files > 0:
            for i, video_file in enumerate(intermediate_mov_files, 1):
                self.check_for_abort("Metadata Correction loop")
                self.update_progress(i, total_files)

                temp_stem = video_file.stem.removesuffix('_gpmf_final')
                original_base_name_candidate = temp_stem.removesuffix(custom_suffix)
                original_360_path = Path(self.settings['SourceDir']) / f"{original_base_name_candidate}.360"

                if not original_360_path.exists():
                    continue

                command = [
                    self.settings['ExifToolPath'],
                    '-TagsFromFile', str(original_360_path),
                    '-time:all>time:all',
                    '-GPSDateTime<GPSDateTime',
                    '-Track*Date>Track*Date',
                    '-P',
                    '-overwrite_original',
                    str(video_file)
                ]

                if self.run_command(command)[0] == 0:
                    self.log_message(f" -> Metadata transferred for {video_file.name}.", 'success')
        else:
            step_counter = self._log_skipped_step(
                3,
                "Transferring metadata",
                "No files"
            )

        return step_counter
        
    def _phase2_max1_export_mp4(self, step_counter, items, custom_suffix):
        """
        Phase 2 - Step 4 (Max 1 only):
        Copies the generated *_gpmf_final.mov files to final .mp4 files in copy mode.
        Returns the updated step_counter.
        """
        step_counter = 4
        self.check_for_abort("Max 1 MP4 Export")
        self.log_message(f"\n[STEP {step_counter}/10] Max 1 CHANNEL: Creating MP4 files (Copy Mode)...", 'info')

        intermediate_mov_files = list(Path(self.settings['TargetDir']).glob("*_gpmf_final.mov"))
        intermediate_mov_files = self._filter_intermediate_mov_files(
            intermediate_mov_files,
            items,
            custom_suffix=custom_suffix
        )

        total_files = len(intermediate_mov_files)
        self.update_progress(0, total_files)

        for i, file in enumerate(intermediate_mov_files, 1):
            self.check_for_abort("Max 1 MP4 Export loop")
            self.update_progress(i, total_files)

            base_name = file.stem
            clean_name = base_name.replace('_gpmf_final', '')

            if self.settings['RunNadirPatch']:
                clean_name += NADIR_SUFFIX

            target_mp4 = Path(self.settings['TargetDir']) / f"{clean_name}.mp4"
            self.log_message(f" -> Copying to: {target_mp4.name}", 'info')

            source_info = self._probe_video_stream_info(file)
            source_codec = self._classify_video_codec(source_info)

            if source_codec == "hevc":
                try:
                    shutil.copy2(file, target_mp4)
                except Exception as e:
                    self.log_message(f" [ERROR] Copy failed: {e}", 'error')
            else:
                self.log_message(f" [MAX1 EXPORT] Source codec is {source_codec}; transcoding to HEVC MP4...", 'info')

                cpu_crf, gpu_qp, _ = self._get_quality_for_source_codec(source_codec)

                if self.settings['UseGPUEncoding']:
                    encoder_choice = self.settings['GPUEncoder'].split(' ')[0]
                    encoder_name = "hevc_nvenc"
                    hwaccel_args = []

                    if encoder_choice == 'qsv':
                        encoder_name = "hevc_qsv"
                        hwaccel_args = ["-hwaccel", "qsv"]
                    elif encoder_choice == 'amf':
                        encoder_name = "hevc_amf"
                    elif encoder_choice in ['nvenc', 'auto']:
                        encoder_name = "hevc_nvenc"

                    cmd_export = [self.settings['FFmpegPath'], "-y"] + hwaccel_args + [
                        "-i", str(file),
                        "-map", "0:v:0",
                        "-map", "0:a?",
                        "-c:v", encoder_name,
                        "-qp", str(gpu_qp),
                        "-tag:v", "hvc1",
                        "-c:a", "copy",
                        str(target_mp4)
                    ]
                else:
                    cmd_export = [
                        self.settings['FFmpegPath'], "-y",
                        "-i", str(file),
                        "-map", "0:v:0",
                        "-map", "0:a?",
                        "-c:v", "libx265",
                        "-preset", "slow",
                        "-x265-params",
                        "aq-mode=3:aq-strength=1.0:psy-rd=2.0:psy-rdoq=2.0:deblock=-1,-1",
                        "-crf", str(cpu_crf),
                        "-tag:v", "hvc1",
                        "-c:a", "copy",
                        str(target_mp4)
                    ]

                if self.run_command(cmd_export, error_message="Max 1 HEVC export failed")[0] != 0:
                    self.log_message(f" [ERROR] HEVC export failed for {file.name}.", 'error')

        return step_counter
        
    def _phase2_max2_generate_gpx(self, step_counter, custom_suffix, items):
        """
        Phase 2 - Step 5 (Max 2 only):
        Generates GPX files from the *_gpmf_final.mov files for SVS preparation.
        Returns the updated step_counter.
        """
        if self.settings['RunCorePrep'] and self.settings['RunGPX']:
            step_counter = 5
            self.check_for_abort("GPX Generation")
            self.log_message(f"\n[STEP {step_counter}/10] {STEP_LABEL_GPX}...", 'info')

            intermediate_mov_files = list(Path(self.settings['TargetDir']).glob("*_gpmf_final.mov"))
            intermediate_mov_files = self._filter_intermediate_mov_files(
                intermediate_mov_files,
                items,
                custom_suffix=custom_suffix
            )
            total_files = len(intermediate_mov_files)
            self.update_progress(0, total_files)

            for i, video_file in enumerate(intermediate_mov_files, 1):
                self.check_for_abort("GPX Generation loop")
                self.update_progress(i, total_files)
                self.log_message(f" -> Generating GPX for file {i}/{total_files}: {video_file.name}", 'info')

                temp_stem = video_file.stem.removesuffix('_gpmf_final')
                final_output_base_name = temp_stem.removesuffix(custom_suffix)
                gpx_output_path = Path(self.settings['SourceDir']) / f"{final_output_base_name}.gpx"

                command = [
                    self.settings['ExifToolPath'],
                    '-p', self.settings['GpxFormatPath'],
                    '-ee',
                    '-m',
                    str(video_file)
                ]

                return_code, output = self.run_command(command, error_message="ExifTool GPX generation failed")

                if return_code == 0 and "<gpx" in output and len(output) > 100:
                    try:
                        with open(gpx_output_path, 'w', encoding='utf-8') as f:
                            f.write(output)
                        self.log_message(f" [SUCCESS] GPX saved: {gpx_output_path.name}", 'success')
                    except Exception as e:
                        self.log_message(f" [ERROR] Error saving GPX: {e}", 'error')
                else:
                    self.log_message(f" [ERROR] GPX generation failed for {video_file.name}.", 'error')
        else:
            step_counter = self._log_skipped_step(
                5,
                "Max 2 CHANNEL: Generating GPX files (SVS Prep)"
            )
        return step_counter
        
    def _phase2_max2_fix_svs_headers(self, step_counter, custom_suffix, items):
        """
        Phase 2 - Step 6 (Max 2 only):
        Creates SVS-compatible MP4 + GPX pairs in the SVS_Fixed_Headers folder
        and synchronizes QuickTime header timestamps based on GPX start time.
        Returns (updated_step_counter, svs_fix_success).
        """
        svs_fix_success = False

        if self.settings['RunCorePrep'] and self.settings['RunSVSHeaderFix'] and self.settings['RunGPX']:
            step_counter = 6
            self.check_for_abort("SVS Header Fix")
            self.log_message(f"\n[STEP {step_counter}/10] {STEP_LABEL_SVS_FIX}...", 'info')

            output_dir = Path(self.settings['TargetDir']) / "SVS_Fixed_Headers"
            output_dir.mkdir(exist_ok=True, parents=True)
            self.log_message(f" [INFO] Fixed files will be saved to: {output_dir.name}", 'info')

            gpx_files_in_source = list(Path(self.settings['SourceDir']).glob("*.gpx"))

            allowed_stems = {item["stem"] for item in items}
            item_by_stem = {item["stem"]: item for item in items}

            gpx_files_in_source = [
                p for p in gpx_files_in_source
                if p.stem in allowed_stems
            ]

            total_files = len(gpx_files_in_source)
            self.update_progress(0, total_files)

            files_fixed_count = 0

            if total_files == 0:
                self.log_message(" [WARNING] No GPX files found. Cannot run SVS Header Fix.", 'warning')

            for i, gpx_path in enumerate(gpx_files_in_source, 1):
                self.check_for_abort("SVS Fix loop")
                self.update_progress(i, total_files)
                self.log_message(f" -> Processing SVS Fix for file {i} of {total_files}: {gpx_path.name}", 'info')

                original_base_name = gpx_path.stem
                current_item = item_by_stem.get(original_base_name)

                if current_item is not None:
                    source_video, source_video_label = self._get_svs_fix_source_video_for_item(
                        current_item,
                        custom_suffix
                    )
                else:
                    mov_name = f"{original_base_name}{custom_suffix}_gpmf_final.mov"
                    source_video = Path(self.settings['TargetDir']) / mov_name
                    source_video_label = "prepared *_gpmf_final.mov"

                if not source_video.exists():
                    self.log_message(
                        f" [ERROR] Source video not found ({source_video_label}). Skipping SVS Fix for {gpx_path.name}.",
                        'error'
                    )
                    continue

                if (
                    current_item is not None
                    and current_item.get("family") == "max1"
                    and current_item.get("time_mode") == "timewarp"
                ):
                    self.log_message(
                        f" [SVS FIX] Max 1 TimeWarp detected; using clean source video for SVS fix: {source_video.name}",
                        'info'
                    )

                source_info = self._probe_video_stream_info(source_video)
                source_codec = self._classify_video_codec(source_info)
                cpu_crf, gpu_qp, _ = self._get_quality_for_source_codec(source_codec)

                svs_file_name_stem = f"{original_base_name}{custom_suffix}"
                if self.settings['RunNadirPatch']:
                    svs_file_name_stem += NADIR_SUFFIX

                if current_item is not None and current_item.get("time_mode") == "timewarp":
                    svs_file_name_stem += "_SVS_TW"
                else:
                    svs_file_name_stem += "_SVS"

                fixed_mp4_path = output_dir / f"{svs_file_name_stem}.mp4"
                fixed_gpx_path = output_dir / f"{svs_file_name_stem}.gpx"

                try:
                    if source_codec == "hevc":
                        self.log_message(" [SVS FIX] Source is already HEVC; stripping internal metadata tracks in copy mode...", 'info')

                        cmd_strip = [
                            self.settings['FFmpegPath'], "-y",
                            "-i", str(source_video),
                            "-map", "0:v",
                            "-map", "0:a?",
                            "-c", "copy",
                            str(fixed_mp4_path)
                        ]

                    else:
                        self.log_message(
                            f" [SVS FIX] Source codec is {source_codec}; transcoding to HEVC before SVS timestamp/header fix...",
                            'info'
                        )

                        if self.settings['UseGPUEncoding']:
                            encoder_choice = self.settings['GPUEncoder'].split(' ')[0]
                            encoder_name = "hevc_nvenc"
                            hwaccel_args = []

                            if encoder_choice == 'qsv':
                                encoder_name = "hevc_qsv"
                                hwaccel_args = ["-hwaccel", "qsv"]
                            elif encoder_choice == 'amf':
                                encoder_name = "hevc_amf"
                            elif encoder_choice in ['nvenc', 'auto']:
                                encoder_name = "hevc_nvenc"

                            cmd_strip = [self.settings['FFmpegPath'], "-y"] + hwaccel_args + [
                                "-i", str(source_video),
                                "-map", "0:v:0",
                                "-map", "0:a?",
                                "-c:v", encoder_name,
                                "-qp", str(gpu_qp),
                                "-tag:v", "hvc1",
                                "-c:a", "copy",
                                str(fixed_mp4_path)
                            ]
                        else:
                            cmd_strip = [
                                self.settings['FFmpegPath'], "-y",
                                "-i", str(source_video),
                                "-map", "0:v:0",
                                "-map", "0:a?",
                                "-c:v", "libx265",
                                "-preset", "slow",
                                "-x265-params",
                                "aq-mode=3:aq-strength=1.0:psy-rd=2.0:psy-rdoq=2.0:deblock=-1,-1",
                                "-crf", str(cpu_crf),
                                "-tag:v", "hvc1",
                                "-c:a", "copy",
                                str(fixed_mp4_path)
                            ]

                    if self.run_command(cmd_strip, error_message="SVS MP4 creation failed")[0] != 0:
                        self.log_message(" [ERROR] FFmpeg MP4 creation/transcode failed. Skipping fix.", 'error')
                        continue

                    shutil.copy2(gpx_path, fixed_gpx_path)

                except Exception as e:
                    self.log_message(f" [ERROR] Could not prepare files for SVS_Fixed_Headers folder: {e}", 'error')
                    continue

                gpx_utc_time, exiftool_time = self._get_first_gpx_time_for_fixer(fixed_gpx_path)
                if not exiftool_time:
                    self.log_message(" [ERROR] Could not get GPX time. Skipping fix.", 'error')
                    continue

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

                fix_code, _ = self.run_command(
                    exiftool_args_fix,
                    error_message="ExifTool SVS Header Fix failed",
                    priority_class=NORMAL_PRIORITY_CLASS
)

                if fix_code == 0 or fix_code == 1:
                    self.log_message(" [SUCCESS] ExifTool header fix applied.", 'success')
                    files_fixed_count += 1
                else:
                    self.log_message(f" [WARNING] ExifTool fix command returned an error (code {fix_code}). Proceeding to verification.", 'warning')

                exiftool_args_verify = [
                    self.settings['ExifToolPath'],
                    "-QuickTime:CreateDate", "-QuickTime:ModifyDate",
                    "-QuickTime:TrackCreateDate", "-QuickTime:TrackModifyDate",
                    "-QuickTime:MediaCreateDate", "-QuickTime:MediaModifyDate",
                    str(fixed_mp4_path)
                ]

                verify_code, verification_output = self.run_command(
                    exiftool_args_verify,
                    error_message="ExifTool SVS Verification failed",
                    priority_class=NORMAL_PRIORITY_CLASS
                )

                log_content = self._generate_verification_log(gpx_utc_time, verification_output, exiftool_time)
                self.log_message(f" [VERIFICATION LOG]\n{log_content}", 'info')

            if files_fixed_count > 0:
                svs_fix_success = True

        else:
            step_counter = self._log_skipped_step(
                6,
                STEP_LABEL_SVS_FIX
            )
        return step_counter, svs_fix_success

    def _phase3_prepare_mapillary_output_dir(self):
        """
        Phase 3 - Preparation:
        Determines whether Mapillary phase 3 should run and prepares the Mapillary_Output directory.
        Returns (temp_mapillary_dir, should_run_phase_3).
        """
        target_root = Path(self.settings['TargetDir'])

        should_run_phase_3 = (
            self.settings['RunSample']
            or self.settings['RunProcess']
            or self.settings['RunUpload']
        )

        if should_run_phase_3:
            specific_subfolder = target_root / "Mapillary_Output"

            if not specific_subfolder.exists():
                try:
                    specific_subfolder.mkdir(parents=True, exist_ok=True)
                    self.log_message(f" [INFO] Created 'Mapillary_Output' folder at: {specific_subfolder}", 'info')
                except Exception as e:
                    self.log_message(f" [WARNING] Could not create 'Mapillary_Output' folder: {e}", 'warning')

            temp_mapillary_dir = specific_subfolder
        else:
            # No Mapillary actions: do not create the folder, only define the path
            temp_mapillary_dir = target_root / "Mapillary_Output"

        return temp_mapillary_dir, should_run_phase_3

    def _phase3_mapillary_sample(self, step_counter, temp_mapillary_dir, items=None, custom_suffix=""):
        """
        Phase 3 - Sampling:
        Samples frames from eligible *_gpmf_final.mov files into the Mapillary output directory.
        Returns the updated step_counter.

        items:
            list of Mapillary-eligible matched items that should be sampled

        custom_suffix:
            suffix used before '_gpmf_final.mov', so we can correctly filter the files
        """
        if self.settings['RunSample']:
            step_counter += 1
            self.check_for_abort("Mapillary Sampling")
            self.log_message(f"\n[STEP {step_counter}/10] {STEP_LABEL_SAMPLE}...", 'info')

            if not temp_mapillary_dir.exists():
                temp_mapillary_dir.mkdir(parents=True)

            intermediate_mov_files = list(Path(self.settings['TargetDir']).glob("*_gpmf_final.mov"))

            if items is not None:
                intermediate_mov_files = self._filter_intermediate_mov_files(
                    intermediate_mov_files,
                    items,
                    custom_suffix=custom_suffix
                )

            total_files = len(intermediate_mov_files)
            self.update_progress(0, total_files)

            if total_files == 0:
                self.log_message(" [WARNING] No eligible *_gpmf_final.mov files found to sample.", 'warning')

            for i, video_file in enumerate(intermediate_mov_files, 1):
                self.check_for_abort("Mapillary Sampling loop")
                self.update_progress(i, total_files)
                self.log_message(f" -> Sampling: {video_file.name}", 'info')

                sampling_args = [
                    self.settings['MapillaryToolsPath'],
                    "sample_video",
                    str(video_file),
                    str(temp_mapillary_dir),
                    f"--video_sample_distance={self.settings['VideoSampleDistance']}"
                ]

                self.run_command(sampling_args, error_message="Mapillary Sampling failed")
        else:
            step_counter += 1
            step_counter = self._log_skipped_step(
                step_counter,
                STEP_LABEL_SAMPLE,
                SKIP_REASON_SAMPLING_DISABLED
            )

        return step_counter

    def _phase3_mapillary_process(self, step_counter, temp_mapillary_dir):
        """
        Phase 3 - Processing:
        Runs mapillary_tools process on the sampled Mapillary output directory.
        Returns the updated step_counter.
        """
        if self.settings['RunProcess']:
            step_counter += 1
            self.check_for_abort("Mapillary Processing")
            self.log_message(f"\n[STEP {step_counter}/10] {STEP_LABEL_PROCESS}...", 'info')

            if temp_mapillary_dir.exists():
                process_args = [
                    self.settings['MapillaryToolsPath'],
                    "process",
                    str(temp_mapillary_dir)
                ]
                self.run_command(process_args, error_message="Mapillary Processing failed")
            else:
                self.log_message(" [WARNING] No frames directory found to process.", 'warning')
        else:
            step_counter += 1
            step_counter = self._log_skipped_step(
                step_counter,
                STEP_LABEL_PROCESS,
                SKIP_REASON_PROCESSING_DISABLED
            )

        return step_counter

    def _phase3_mapillary_upload(self, step_counter, temp_mapillary_dir):
        """
        Phase 3 - Upload:
        Uploads processed Mapillary sequences either as one batch (root JSON present)
        or per subfolder (sequence-by-sequence).
        Returns the updated step_counter.
        """
        step_counter = max(step_counter, 8) + 1

        if self.settings['RunUpload']:
            self.check_for_abort("Mapillary Upload")
            self.log_message(f"\n[STEP {step_counter}/10] {STEP_LABEL_UPLOAD}...", 'info')

            user_arg = self.settings.get('MapillaryUserName', '').strip()
            if not user_arg:
                self.log_message(" [ERROR] Mapillary Profile Name is empty. Please fill it in Configuration.", 'error')
                return step_counter

            self.log_message(f" [INFO] Using configured Mapillary profile name: {user_arg}", 'info')

            if not temp_mapillary_dir.exists():
                self.log_message(f" [ERROR] Cannot upload. Directory not found: {temp_mapillary_dir}", 'error')
                return step_counter

            root_desc_file = temp_mapillary_dir / "mapillary_image_description.json"

            # ============================================================
            # SITUATION 1: JSON in root -> batch upload
            # ============================================================
            if root_desc_file.exists():
                self.log_message(" [INFO] Global description file found in root. Uploading entire batch...", 'info')

                upload_args = [
                    self.settings['MapillaryToolsPath'],
                    "upload",
                    "--user_name", user_arg,
                    str(temp_mapillary_dir)
                ]

                exit_code, output = self.run_command(upload_args)

                if exit_code != 0:
                    self.log_message(" [ERROR] Upload failed or nothing uploaded. Check logs above.", 'error')
                    self.log_mapillary_account_help()
                else:
                    self.log_message(" [SUCCESS] Batch upload process finished.", 'success')

            # ============================================================
            # SITUATION 2: subfolders -> per sequence upload
            # ============================================================
            else:
                self.log_message(" [INFO] No root JSON found. Checking individual subfolders...", 'info')

                seq_dirs = [d for d in temp_mapillary_dir.iterdir() if d.is_dir()]

                if not seq_dirs:
                    self.log_message(f" [WARNING] No folders found in {temp_mapillary_dir.name}.", 'warning')

                for i, seq_dir in enumerate(seq_dirs, 1):
                    self.check_for_abort("Mapillary Upload loop")

                    if not (seq_dir / "mapillary_image_description.json").exists():
                        self.log_message(f" [WARNING] Skipping {seq_dir.name}: No description file found.", 'warning')
                        continue

                    self.log_message(f" -> Uploading sequence: {seq_dir.name}...", 'info')

                    upload_args = [
                        self.settings['MapillaryToolsPath'],
                        "upload",
                        "--user_name", user_arg,
                        str(seq_dir)
                    ]

                    exit_code, output = self.run_command(upload_args)

                    if exit_code != 0:
                        self.log_message(f" [ERROR] Upload failed for {seq_dir.name}.", 'error')
                        self.log_mapillary_account_help()
                    else:
                        self.log_message(f" [SUCCESS] Uploaded {seq_dir.name}.", 'success')

        else:
            mapillary_phase_enabled = (
                self.settings['RunSample']
                or self.settings['RunProcess']
                or self.settings['RunUpload']
            )
            reason = (
                SKIP_REASON_MAPILLARY_DISABLED
                if not mapillary_phase_enabled
                else SKIP_REASON_UPLOAD_DISABLED
            )
            step_counter = self._log_skipped_step(
                step_counter,
                STEP_LABEL_UPLOAD,
                reason
            )

        return step_counter

    def _phase4_cleanup(self, step_counter, temp_mapillary_dir, custom_suffix, gpx_cleanup_items):
        """
        Phase 4 - Cleanup:
        Removes temporary/derived files and renames Mapillary sequence folders.
        Returns the updated step_counter.

        gpx_cleanup_items:
            items for which GPX files were created in SourceDir during this run
            (standard Max 2 GPX + supported TimeWarp GPX)
        """
        # Cleanup is skipped in Upload Only mode (RunCorePrep == False)
        if self.settings['RunCorePrep']:
            step_counter += 1
            self.check_for_abort("Final Cleanup")
            self.update_progress(100, 100)
            self.log_message(f"\n[STEP {step_counter}/10] Final cleanup and renaming...", 'info')

            # A. Remove GPX files generated in SourceDir for this run
            if self.settings.get('RunGPX', False) and gpx_cleanup_items:
                source_dir = Path(self.settings['SourceDir'])

                expected_gpx_files = []
                seen_stems = set()

                for item in gpx_cleanup_items:
                    stem = item.get("stem")
                    if not stem or stem in seen_stems:
                        continue
                    seen_stems.add(stem)
                    expected_gpx_files.append(source_dir / f"{stem}.gpx")

                gpx_files_to_clean = [p for p in expected_gpx_files if p.exists()]

                if gpx_files_to_clean:
                    self.log_message(f" -> Cleaning up {len(gpx_files_to_clean)} GPX files...", 'info')
                    for f in gpx_files_to_clean:
                        try:
                            os.remove(f)
                            self.log_message(f" [INFO] Removed GPX: {f.name}", 'success')
                        except Exception as e:
                            self.log_message(f" [WARNING] Could not delete GPX {f.name}: {e}", 'warning')
                else:
                    self.log_message(" [INFO] No GPX files found to clean for this run.", 'info')

            # B. Remove intermediate *_gpmf_final.mov files
            mov_files_to_clean = list(Path(self.settings['TargetDir']).glob("*_gpmf_final.mov"))
            if mov_files_to_clean:
                self.log_message(f" -> Cleaning up {len(mov_files_to_clean)} intermediate .mov files...", 'info')
                for f in mov_files_to_clean:
                    try:
                        os.remove(f)
                        self.log_message(f" [INFO] Removed MOV: {f.name}", 'success')
                    except Exception as e:
                        self.log_message(f" [WARNING] Could not delete {f.name}: {e}", 'warning')

            # C. Remove TimeWarp GPX work directory
            timewarp_gpx_dir = Path(self.settings['TargetDir']) / TIMEWARP_SVS_GPX_DIR_NAME
            if timewarp_gpx_dir.exists():
                try:
                    shutil.rmtree(timewarp_gpx_dir, ignore_errors=False)
                    self.log_message(f" [INFO] Removed TimeWarp GPX work dir: {timewarp_gpx_dir.name}", 'success')
                except Exception as e:
                    self.log_message(
                        f" [WARNING] Could not delete TimeWarp GPX work dir {timewarp_gpx_dir.name}: {e}",
                        'warning'
                    )

            # D. Rename Mapillary folders
            if temp_mapillary_dir.exists() and (self.settings['RunProcess'] or self.settings['RunUpload']):
                self.log_message(" [INFO] Renaming sequences...", 'info')
                temp_sequence_dirs = [d for d in temp_mapillary_dir.iterdir() if d.is_dir()]

                for seq_dir in temp_sequence_dirs:
                    original_name = seq_dir.name
                    new_name = original_name

                    if '_gpmf_final' in new_name:
                        new_name = new_name.replace('_gpmf_final', '')

                    if new_name.endswith('.mov'):
                        new_name = new_name[:-4]

                    final_seq_name = new_name

                    if self.settings['RunNadirPatch'] and 'NADIR_SUFFIX' in globals() and NADIR_SUFFIX not in final_seq_name:
                        final_seq_name += NADIR_SUFFIX

                    if final_seq_name != original_name and final_seq_name:
                        new_path = seq_dir.parent / final_seq_name
                        try:
                            seq_dir.rename(new_path)
                            self.log_message(
                                f" [SUCCESS] Renamed sequence folder: {original_name} -> {final_seq_name}",
                                'success'
                            )
                        except Exception as e:
                            self.log_message(
                                f" [WARNING] Could not rename {original_name} -> {final_seq_name}: {e}",
                                'warning'
                            )
            else:
                self.log_message(" [INFO] No Mapillary folder renaming needed.", 'info')

        else:
            step_counter += 1
            step_counter = self._log_skipped_step(
                step_counter,
                "Final cleanup and renaming",
                SKIP_REASON_CORE_PREP_DISABLED
            )

        return step_counter
    
    def _process_ui_queue(self):
        """
        Processes queued UI events on the Tkinter main thread.
        """
        try:
            while not self.ui_queue.empty():
                item = self.ui_queue.get_nowait()
                event_type = item[0]

                if event_type == "log":
                    _, message, message_type, extended_only = item
                    self._log_message_ui(message, message_type, extended_only)

                elif event_type == "progress":
                    _, current_step, total_steps = item
                    self._update_progress_ui(current_step, total_steps)

                elif event_type == "messagebox":
                    _, level, title, message = item
                    if level == "info":
                        messagebox.showinfo(title, message)
                    elif level == "warning":
                        messagebox.showwarning(title, message)
                    elif level == "error":
                        messagebox.showerror(title, message)

                elif event_type == "stop_button":
                    _, state = item
                    if self.stop_button:
                        self.stop_button.config(state=state)

        except Exception as e:
            print(f"[UI QUEUE ERROR] {e}")

        self.master.after(100, self._process_ui_queue)
    
    def _log_skipped_step(self, step_number, label, reason=None):
        """
        Logs a workflow step as skipped and returns the step number
        so the caller can keep the step counter aligned.
        """
        msg = f"\n[STEP {step_number}/10] {label} SKIPPED"
        if reason:
            msg += f" ({reason})"
        msg += "."
        self.log_message(msg, 'info')
        return step_number
    
    def _finalize_max_workflow(
        self,
        start_time,
        svs_fix_success,
        processed_items=None,
        rejected_items=None,
        orphan_360=None,
        orphan_videos=None
    ):
        """
        Builds and shows the final completion summary for the Max workflow.

        Popup:
            short completion message with accepted / failed counts

        Log:
            full accepted / rejected / unmatched summary
        """
        processed_items = processed_items or []
        rejected_items = rejected_items or []
        orphan_360 = orphan_360 or []
        orphan_videos = orphan_videos or []

        end_time = datetime.now()
        elapsed_time = end_time - start_time
        total_seconds = int(elapsed_time.total_seconds())
        formatted_time = f"{total_seconds // 3600:02}:{(total_seconds % 3600) // 60:02}:{total_seconds % 60:02}"

        ok_count = len(processed_items)
        fail_count = len(rejected_items) + len(orphan_360) + len(orphan_videos)

        final_summary_message = (
            f"Workflow completed.\n\n"
            f"Succeeded / good: {ok_count}\n"
            f"Failed / error: {fail_count}\n"
            f"Time: {formatted_time}"
        )

        if self.settings['RunSVSHeaderFix'] and svs_fix_success:
            svs_upload_dir = Path(self.settings['TargetDir']) / "SVS_Fixed_Headers"
            if svs_upload_dir.exists() and any(svs_upload_dir.iterdir()):
                final_summary_message += f"\n\nSVS output folder:\n{svs_upload_dir.name}"

        self._log_accept_reject_summary(
            processed_items,
            rejected_items,
            orphan_360=orphan_360,
            orphan_videos=orphan_videos
        )

        self.log_message("\n=======================================================", 'success')
        self.log_message(f" WORKFLOW COMPLETE! Time: {formatted_time}", 'success')
        self.log_message("=======================================================\n", 'success')

        self.show_messagebox("info", "Done", final_summary_message)
    
    def _validate_and_run_max_workflow(self):
        """
        Worker-thread entrypoint:
        1) do deep validation / inventory build
        2) abort early if invalid
        3) run normal workflow
        """
        try:
            self.log_message("--- DEEP VALIDATING FOR MAX ---", 'info')

            ok, inventory = self.validate_runtime_deep_max()
            if not ok:
                self.log_message("[FATAL] Deep validation failed. Workflow aborted.", 'error')
                return

            # Store inventory so run_workflow can reuse it
            self.settings['_validated_inventory'] = inventory

            self.run_workflow()

        except UserAbortException:
            self.log_message("[INFO] Workflow aborted by user during deep validation.", 'warning')
        except Exception as e:
            self.log_message(f"[FATAL] Unexpected error during deep validation: {e}", 'error')
        finally:
            self.master.after(0, self._cleanup_after_workflow)
        
    def run_workflow(self):
        """The core execution logic (Max Workflow) with auto-detected Max 1 / Max 2 family routing."""
        try:
            start_time = datetime.now()
            self.settings['StartTime'] = start_time
            self.settings['TotalVideosProcessed'] = 0
            self.settings['TotalImagesProcessed'] = 0

            inventory = self.settings.get('_validated_inventory')
            if not inventory:
                inventory = self._build_max_source_inventory(
                    log_selection=False,
                    log_warnings=False,
                    log_detection=False
                )
            
            self.settings['_validated_inventory'] = None

            all_items = inventory.get("accepted_items", inventory["matched_items"])
            rejected_items = inventory.get("rejected_items", [])
            orphan_360 = inventory.get("orphan_360", [])
            orphan_videos = inventory.get("orphan_videos", [])

            if not all_items and not orphan_360 and not orphan_videos:
                self.log_message("[FATAL] No supported files available for processing.", 'error')
                return

            max1_items = [x for x in all_items if x["family"] == "max1"]
            max2_items = [x for x in all_items if x["family"] == "max2"]
            unknown_items = [x for x in all_items if x["family"] == "unknown"]

            accepted_timewarp_items = [
                item for item in all_items
                if item.get("time_mode") == "timewarp"
            ]

            standard_max2_items = [
                item for item in max2_items
                if item.get("time_mode") != "timewarp"
            ]

            standard_max1_items = [
                item for item in max1_items
                if item.get("time_mode") != "timewarp"
            ]

            mapillary_items = [
                item for item in all_items
                if item.get("time_mode") != "timewarp"
            ]

            if accepted_timewarp_items:
                self.log_message("", 'info')
                self.log_message("[INFO] Supported TimeWarp files will continue through the SVS/core workflow:", 'info')

                for item in accepted_timewarp_items:
                    self.log_message(
                        f"  - {item['video_source'].name}: "
                        f"TimeWarp {item['timewarp_rate']}X "
                        f"(Rate={item.get('time_mode_raw_rate')}, "
                        f"Video FPS={item.get('time_mode_output_fps'):.2f}, "
                        f"Effective FPS={item.get('time_mode_effective_unique_fps'):.2f})",
                        'info'
                    )

                self.log_message(
                    "[INFO] Supported TimeWarp items are temporarily excluded from Mapillary.",
                    'warning'
                )

            if rejected_items:
                self.log_message("", 'info')
                self.log_message(
                    f"[INFO] {len(rejected_items)} unsupported file(s) will be skipped. "
                    "A full accept/reject summary will be shown at the end.",
                    'warning'
                )

            self.log_message("[INFO] Workflow started with the following settings:", 'info')
            self.log_message("  Camera Family Detection: AUTO", 'info')
            self.log_message(
                f"  Detected Max Families -> Max 1: {len(max1_items)} | Max 2: {len(max2_items)} | Unknown: {len(unknown_items)}",
                'info'
            )
            self.log_message(f"  Core Prep RUN: {self.settings['RunCorePrep']}", 'info')
            self.log_message(f"  GPX Generation RUN: {self.settings['RunGPX']}", 'info')
            self.log_message(f"  SVS Output RUN: {self.settings['RunSVSHeaderFix']}", 'info')
            self.log_message(f"  Mapillary Workflow RUN: {self.settings['RunSample']}", 'info')
            self.log_message(f"  Nadir Patch RUN: {self.settings['RunNadirPatch']}", 'info')

            custom_suffix = f"_{self.settings['FileSuffix']}" if self.settings['FileSuffix'] else ""

            nadir_work = Path(self.settings['TargetDir']) / "nadir_work"
            if self.settings['RunNadirPatch']:
                nadir_work.mkdir(exist_ok=True)

            step_counter = 0

            # ==============================================================================
            # PHASE 1: COMMON PREPARATION FOR ALL MATCHED ITEMS
            # ==============================================================================
            if self.settings['RunCorePrep']:
                step_counter = self._phase1_extract_gpmf(step_counter, all_items)
                step_counter = self._phase1_mux_video_and_gpmf(step_counter, custom_suffix, nadir_work, all_items)
                step_counter = self._phase1_transfer_metadata(step_counter, custom_suffix, all_items)
            else:
                step_counter = self._log_skipped_step(1, "Extracting GPMF metadata", SKIP_REASON_CORE_PREP_DISABLED)
                step_counter = self._log_skipped_step(2, STEP_LABEL_MUX, SKIP_REASON_CORE_PREP_DISABLED)
                step_counter = self._log_skipped_step(3, "Transferring metadata", SKIP_REASON_CORE_PREP_DISABLED)

            # ==============================================================================
            # PHASE 2A: MAX 1 CHANNEL
            # ==============================================================================
            if standard_max1_items:
                step_counter = self._phase2_max1_export_mp4(step_counter, standard_max1_items, custom_suffix)
            else:
                step_counter = self._log_skipped_step(
                    4,
                    "Max 1 CHANNEL: Creating MP4 files (Copy Mode)",
                    "No standard Max 1 items detected"
                )

            # ==============================================================================
            # PHASE 2B: STANDARD MAX 2 CHANNEL
            # ==============================================================================
            svs_fix_success = False

            if standard_max2_items:
                step_counter = self._phase2_max2_generate_gpx(step_counter, custom_suffix, standard_max2_items)
            else:
                step_counter = self._log_skipped_step(
                    5,
                    STEP_LABEL_GPX,
                    SKIP_REASON_NO_MAX2_ITEMS
                )

            # ------------------------------------------------------------------------------
            # TIMEWARP SVS NORMALIZATION (Max 1 + Max 2 supported TimeWarp only)
            # ------------------------------------------------------------------------------
            timewarp_items_ready_for_svs_fix = []
            if accepted_timewarp_items:
                timewarp_items_ready_for_svs_fix = self._prepare_timewarp_svs_gpxs(
                    accepted_timewarp_items,
                    custom_suffix
                )

            svs_fix_items = list(standard_max2_items) + list(timewarp_items_ready_for_svs_fix)

            if svs_fix_items:
                step_counter, svs_fix_success = self._phase2_max2_fix_svs_headers(
                    step_counter,
                    custom_suffix,
                    svs_fix_items
                )
            else:
                step_counter = self._log_skipped_step(
                    6,
                    STEP_LABEL_SVS_FIX,
                    SKIP_REASON_NO_MAX2_ITEMS
                )

            # ==============================================================================
            # PHASE 3: MAPILLARY PROCESSING
            # ==============================================================================
            temp_mapillary_dir, should_run_phase_3 = self._phase3_prepare_mapillary_output_dir()
            has_mapillary_eligible_items = len(mapillary_items) > 0

            if should_run_phase_3 and has_mapillary_eligible_items:
                step_counter = self._phase3_mapillary_sample(
                    step_counter,
                    temp_mapillary_dir,
                    items=mapillary_items,
                    custom_suffix=custom_suffix
                )
                step_counter = self._phase3_mapillary_process(step_counter, temp_mapillary_dir)

            elif should_run_phase_3 and not has_mapillary_eligible_items:
                self.log_message(
                    "[INFO] Mapillary phase enabled, but no Mapillary-eligible standard video items remain.",
                    'warning'
                )
                step_counter = self._log_skipped_step(
                    7,
                    STEP_LABEL_SAMPLE,
                    SKIP_REASON_TIMEWARP_MAPILLARY_DEFERRED
                )
                step_counter = self._log_skipped_step(
                    8,
                    STEP_LABEL_PROCESS,
                    SKIP_REASON_TIMEWARP_MAPILLARY_DEFERRED
                )

            else:
                step_counter = self._log_skipped_step(
                    7,
                    STEP_LABEL_SAMPLE,
                    SKIP_REASON_MAPILLARY_DISABLED
                )
                step_counter = self._log_skipped_step(
                    8,
                    STEP_LABEL_PROCESS,
                    SKIP_REASON_MAPILLARY_DISABLED
                )

            # ==============================================================================
            # PHASE 4: MAPILLARY UPLOAD
            # ==============================================================================
            if has_mapillary_eligible_items:
                step_counter = self._phase3_mapillary_upload(step_counter, temp_mapillary_dir)
            elif self.settings['RunUpload']:
                step_counter = self._log_skipped_step(
                    9,
                    STEP_LABEL_UPLOAD,
                    SKIP_REASON_TIMEWARP_MAPILLARY_DEFERRED
                )
            else:
                step_counter = self._phase3_mapillary_upload(step_counter, temp_mapillary_dir)

            # ==============================================================================
            # PHASE 5 / STEP 10: FINAL CLEANUP
            # ==============================================================================
            step_counter = self._phase4_cleanup(
                step_counter,
                temp_mapillary_dir,
                custom_suffix,
                svs_fix_items
            )

            self._finalize_max_workflow(
                start_time,
                svs_fix_success,
                processed_items=all_items,
                rejected_items=rejected_items,
                orphan_360=orphan_360,
                orphan_videos=orphan_videos
            )

        except UserAbortException:
            self.log_message("[WARNING] Workflow manually aborted by user.", 'warning')
        except Exception as e:
            self.log_message(f"[FATAL] Unhandled workflow error: {e}", 'error')
            self.ui_queue.put(("messagebox", "error", "Workflow Error", str(e)))
        finally:
            self._reset_analysis_cache()
            self.ui_queue.put(("stop_button", tk.DISABLED))
            self.running_thread = None

    # ============================================
    # HERO WORKFLOW HELPERS
    # ============================================
    def _hero_collect_items(self):
        """
        Collects Hero workflow items and determines whether the workflow runs in
        file mode (sampling from source videos) or folder mode (process/upload from target folders).
        Returns (items_to_process, is_file_mode, src, tgt).
        """
        src = Path(self.settings['HeroSourceDir'])
        tgt = Path(self.settings['HeroTargetDir'])

        if not tgt.exists():
            tgt.mkdir(parents=True)

        items_to_process = []
        is_file_mode = False

        if self.settings['RunSample']:
            self.log_message("Mode: Full Workflow (Sampling from Source)", 'info')
            raw_files = list(src.glob("*.mp4"))
            items_to_process = sorted(raw_files, key=lambda x: x.name)
            is_file_mode = True

            if not items_to_process:
                self.log_message("[ERROR] No .mp4 files found in Hero Source.", 'error')
                return [], is_file_mode, src, tgt
        else:
            self.log_message("Mode: Upload/Process Only (Scanning Target Dir)", 'info')

            if tgt.exists():
                raw_items = list(tgt.iterdir())
                for item in raw_items:
                    if not item.is_dir():
                        continue
                    if item.name in ["Upload_Successful", "System Volume Information", "$RECYCLE.BIN", "RECYCLER"]:
                        continue
                    if item.name.startswith("."):
                        continue
                    items_to_process.append(item)

            items_to_process.sort(key=lambda x: x.name)
            self.log_message(f"[INFO] Found {len(items_to_process)} folders to process.", 'info')

            if not items_to_process:
                self.log_message("[ERROR] No suitable folders found in Hero Target to process/upload.", 'error')
                return [], is_file_mode, src, tgt

        return items_to_process, is_file_mode, src, tgt
        
    def _hero_prepare_paths(self, item, tgt, is_file_mode):
        """
        Prepares the working paths for a Hero workflow item.
        Returns (video_frames_dir, video_stem, temp_sample_dir).
        """
        if is_file_mode:
            video_stem = item.stem
            custom_suffix = f"_{self.settings['FileSuffix']}" if self.settings['FileSuffix'] else ""
            final_sequence_name = f"{video_stem}{custom_suffix}"
            video_frames_dir = tgt / final_sequence_name
            temp_sample_dir = tgt / video_stem
        else:
            video_frames_dir = item
            video_stem = item.name
            temp_sample_dir = item

        return video_frames_dir, video_stem, temp_sample_dir

    def _hero_sample_video(self, item, item_name, temp_sample_dir, video_frames_dir):
        """
        Samples a Hero source video and normalizes the resulting folder structure.
        Returns (success, final_video_frames_dir).
        """
        self.check_for_abort(f"Hero Sampling ({item_name})")
        self.log_message(" -> Sampling from video...", 'info')

        cmd_sample = [
            self.settings['MapillaryToolsPath'],
            "sample_video",
            str(item),
            str(temp_sample_dir),
            "--video_sample_distance",
            str(self.settings['VideoSampleDistance'])
        ]

        c, _ = self.run_command(cmd_sample)
        if c != 0:
            return False, video_frames_dir

        actual_sample_subfolder = temp_sample_dir / item_name
        if actual_sample_subfolder.exists():
            self.log_message(" -> Correcting nested directory structure...", 'info')
            for sub_item in actual_sample_subfolder.iterdir():
                shutil.move(str(sub_item), str(temp_sample_dir / sub_item.name))
            shutil.rmtree(actual_sample_subfolder, ignore_errors=True)

        if temp_sample_dir != video_frames_dir:
            try:
                if video_frames_dir.exists():
                    shutil.rmtree(video_frames_dir)
                temp_sample_dir.rename(video_frames_dir)
                self.log_message(f" -> Renamed folder to: {video_frames_dir.name}", 'info')
            except Exception as e:
                self.log_message(f" [ERROR] Could not rename folder: {e}. Keeping original name.", 'error')
                video_frames_dir = temp_sample_dir

        return True, video_frames_dir
 
    def _hero_process_and_upload(self, video_frames_dir, video_stem, upload_success_dir):
        """
        Processes and optionally uploads a Hero sequence folder.
        Returns True if the flow may continue, False if processing/upload failed hard for this item.
        """
        if self.settings['RunProcess']:
            if not video_frames_dir.exists():
                self.log_message(f" [WARNING] Cannot process. Directory not found: {video_frames_dir.name}", 'warning')
                return False

            self.check_for_abort(f"Hero Processing ({video_stem})")
            self.log_message(f" -> Processing frames (generating JSON) in {video_frames_dir.name}...", 'info')

            cmd_process = [self.settings['MapillaryToolsPath'], "process", str(video_frames_dir)]
            c, _ = self.run_command(cmd_process)
            if c != 0:
                self.log_message(f" [ERROR] Processing failed for {video_frames_dir.name}", 'error')
                return False

        if self.settings['RunUpload']:
            if not video_frames_dir.exists():
                self.log_message(f" [ERROR] Cannot upload. Directory not found: {video_frames_dir}", 'error')
                return False

            if not (video_frames_dir / "mapillary_image_description.json").exists():
                self.log_message(f" [ERROR] No description file found in {video_frames_dir.name}. Processing likely failed.", 'error')
                return False

            self.check_for_abort(f"Hero Upload ({video_stem})")
            self.log_message(" -> Uploading...", 'info')

            cmd_upload = [
                self.settings['MapillaryToolsPath'],
                "upload",
                str(video_frames_dir),
                "--user_name", self.settings['MapillaryUserName'],
                f"--num_upload_workers={self.settings['MapillaryUploadWorkers']}"
            ]

            c, _ = self.run_command(cmd_upload)

            if c == 0:
                self.log_message(f" -> Upload Success! Moving to {upload_success_dir.name}...", 'success')
                upload_success_dir.mkdir(exist_ok=True)
                try:
                    destination = upload_success_dir / video_frames_dir.name
                    if destination.exists():
                        shutil.rmtree(destination)
                    shutil.move(str(video_frames_dir), str(upload_success_dir))
                except Exception as e:
                    self.log_message(f" [WARNING] Move failed: {e}", 'warning')
            else:
                self.log_message(f" [ERROR] Upload failed. Frames remain in {video_frames_dir.name}", 'error')
                self.log_mapillary_account_help()

        return True
 
    def run_hero_workflow_logic(self):
        try:
            start_time = datetime.now()
            self.log_message("--- STARTING GOPRO HERO WORKFLOW ---", 'info')

            items_to_process, is_file_mode, src, tgt = self._hero_collect_items()
            if not items_to_process:
                return

            total = len(items_to_process)
            upload_success_dir = tgt / "Upload_Successful"

            self.update_progress(0, total)

            for i, item in enumerate(items_to_process, 1):
                item_name = item.name
                self.check_for_abort(f"Hero Loop ({item_name})")

                pct = self.update_progress(i, total)
                self.log_message(f"\nProcessing item {i}/{total} ({pct:.1f}%): {item_name}", 'info')

                video_frames_dir, video_stem, temp_sample_dir = self._hero_prepare_paths(item, tgt, is_file_mode)

                if self.settings['RunSample'] and is_file_mode:
                    ok, video_frames_dir = self._hero_sample_video(item, item_name, temp_sample_dir, video_frames_dir)
                    if not ok:
                        continue

                ok = self._hero_process_and_upload(video_frames_dir, video_stem, upload_success_dir)
                if not ok:
                    continue

            elapsed = datetime.now() - start_time
            self.log_message(f"--- HERO WORKFLOW FINISHED ({elapsed}) ---", 'success')
            self.show_messagebox("info", "Done", "GoPro Hero Workflow Complete")

        except UserAbortException as e:
            self.log_message(f"\n[WORKFLOW ABORTED] {e}", 'error')
            self.show_messagebox("warning", "Aborted", "The Hero Workflow was manually stopped.")

        except Exception as e:
            self.log_message(f"\n[FATAL ERROR] Hero workflow thread crashed: {e}", 'error')
            self.show_messagebox("error", "Fatal Error", f"Hero workflow thread crashed:\n{e}")

        finally:
            self._reset_analysis_cache()
            self.ui_queue.put(("stop_button", tk.DISABLED))
            self.running_thread = None
        
if __name__ == "__main__":
    FIXED_BG_COLOR = '#E8E8E8'
    ACTIVE_BG_COLOR = '#D8D8D8'
    ORANGE_BUTTON_COLOR = '#EC9C4E'
    HOVER_BUTTON_COLOR = '#47A9A3'

    BUTTON_FONT = ('Arial', 10, 'bold')
    HEADER_FONT = ('Arial', 10, 'bold')

    try:
        # 1) Root correct aanmaken (FIXT jouw huidige SyntaxError regel)
        root = tk.Tk()
        root.configure(bg=FIXED_BG_COLOR)

        # 2) Splash state (mutable zodat we geen nonlocal nodig hebben)
        splash_state = {
            "active": False,
            "start": None,
            "close": None
        }

        # 3) Alleen in EXE: splash tonen en root verbergen
        if getattr(sys, 'frozen', False):
            root.withdraw()
            splash_state["active"] = True
            splash_state["start"] = time.perf_counter()

            # show_splash gebruikt max_ms (niet duration_ms)
            splash_state["close"] = show_splash(
                root,
                APP_VERSION,
                max_ms=SPLASH_MAX_MS,      # max 10s fallback
                bg_color=FIXED_BG_COLOR,
                image_name=SPLASH_IMAGE
            )

        def finalize_show(err=None):
            """
            Sluit splash (respecteer minimale splash tijd) en toon main window.
            Indien err: toon foutmelding.
            """
            def do_show():
                # 1) Splash sluiten als die er nog is
                if splash_state.get("close"):
                    try:
                        splash_state["close"]()                    
                    except Exception:
                        pass
                    splash_state["close"] = None

                # 2) Hoofdvenster tonen (niet force-focus)
                try:
                    root.deiconify()
                except Exception:
                    pass

                # 3) Foutmelding tonen als er een exception was
                if err is not None:
                    try:
                        messagebox.showerror(
                            "Startup Error",
                            f"Application failed to start:\n\n{type(err).__name__}: {err}"
                        )
                    except Exception:
                        pass

            # Respecteer minimale splash tijd (alleen als splash actief was)
            if splash_state.get("active") and splash_state.get("start") is not None:
                elapsed_ms = int((time.perf_counter() - splash_state["start"]) * 1000)
                remaining_ms = max(0, SPLASH_MIN_MS - elapsed_ms)
                root.after(remaining_ms, do_show)
            else:
                do_show()

        def launch_main_ui():
            """
            Bouw UI. Sluit splash altijd (succes of error), met min splash tijd.
            """
            err = None
            try:
                # --- jouw bestaande ttk styling code ---
                style = ttk.Style(root)
                try:
                    style.theme_use('clam')

                    style.configure('TFrame', background=FIXED_BG_COLOR)
                    style.configure('TLabelframe', background=FIXED_BG_COLOR)
                    style.configure('TLabelframe.Label', font=HEADER_FONT, background=FIXED_BG_COLOR, foreground='black')

                    style.configure('TButton', font=BUTTON_FONT, background=ORANGE_BUTTON_COLOR, borderwidth=1, relief="raised")
                    style.map('TButton', background=[('active', HOVER_BUTTON_COLOR), ('!disabled', ORANGE_BUTTON_COLOR)])

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

                    style.configure('TNotebook', background=FIXED_BG_COLOR, borderwidth=0)
                    style.configure('TNotebook.Tab', background=FIXED_BG_COLOR, foreground='black', borderwidth=1, focuscolor=FIXED_BG_COLOR)
                    style.map('TNotebook.Tab',
                              background=[('selected', FIXED_BG_COLOR), ('active', ACTIVE_BG_COLOR)],
                              foreground=[('selected', 'black')])

                    style.configure('Accent.Big.TButton',
                                    font=('Arial', 12, 'bold'),
                                    foreground='black',
                                    background=ORANGE_BUTTON_COLOR,
                                    padding=[20, 11, 20, 11])
                    style.map('Accent.Big.TButton',
                              background=[('active', HOVER_BUTTON_COLOR), ('!disabled', ORANGE_BUTTON_COLOR)])

                    style.configure('Stop.TButton',
                                    font=BUTTON_FONT,
                                    background='red',
                                    foreground='white',
                                    borderwidth=1,
                                    relief="raised")
                    style.map('Stop.TButton',
                              background=[('active', '#CC0000'), ('!disabled', 'red')],
                              foreground=[('active', 'white'), ('!disabled', 'white')])

                    style.configure("Main.Horizontal.TProgressbar",
                                    troughcolor='white',
                                    background='#32CD32',
                                    bordercolor='#999999',
                                    lightcolor='#32CD32',
                                    darkcolor='#32CD32',
                                    thickness=20)

                except Exception as e:
                    print(f"Warning: Failed to apply ttk styling changes: {e}")

                root.update_idletasks()

                # --- App bouwen (kan exceptions gooien) ---
                _ = MapillaryApp(root, FIXED_BG_COLOR)

            except Exception as e:
                err = e
                import traceback
                traceback.print_exc()

            finally:
                # Splash altijd sluiten (ook bij error) + window tonen
                finalize_show(err)

        # Start UI build with a small delay so the splash animation can start
        root.after(200, launch_main_ui)

        root.mainloop()

    except tk.TclError as e:
        error_msg = (
            "FATAL ERROR (Tcl/Tk): The graphical interface could not be started.\n\n"
            f"Specific Error:\n{e}\n\nEnsure Python is installed correctly."
        )
        print(error_msg)
        try:
            import tkinter.messagebox
            root_err = tk.Tk()
            root_err.withdraw()
            tkinter.messagebox.showerror("Fatal Tcl/Tk Error", error_msg)
        except Exception:
            pass
        sys.exit(1)

    except Exception as e:
        import traceback
        traceback.print_exc()
        print("\n\n[FATAL ERROR] The application crashed with an unexpected error.")
        print(f"Error Type: {type(e).__name__}")
        print(f"Error Message: {e}")
        try:
            tk.messagebox.showerror("Fatal Error", f"The application crashed with an unexpected error:\n{e}")
        except Exception:
            pass
        sys.exit(1)