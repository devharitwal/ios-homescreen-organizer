import asyncio
import json
import math
import os
import threading
import tkinter as tk
from tkinter import messagebox, ttk, simpledialog
from datetime import datetime
import io
from PIL import Image, ImageDraw, ImageFont, ImageTk
from pymobiledevice3.lockdown import create_using_usbmux
from pymobiledevice3.services.springboard import SpringBoardServicesService

# ---------- Theme ----------
BG = "#1e1e1e"
FG = "#f0f0f0"
HIGHLIGHT = "#3a6fb8"
ENTRY_BG = "#2b2b2b"
CARD_BG = "#262626"
FOLDER_BG = "#2f2f2f"
FOLDER_PREVIEW = "#3d3d3d"
GHOST_BG = "#101010"
MUTED = "#777777"
HEADER_FG = "#4fc3f7"
FOLDER_NAME_FG = "#f0c060"

# ---------- Sizes ----------
ICON_LIST = 52        # app list on the left
ICON_TILE = 68        # apps on home screen pages and dock
ICON_MINI = 24        # mini icons inside folder previews
ICON_OVERLAY = 76     # apps inside the open folder window
ICON_DRAG = 92        # icon that follows the cursor while dragging
TILE_W = 116
TILE_H = 124
COLS = 4              # icon columns per page
MIN_ROWS = 6          # empty rows shown on each page
PAGES_PER_ROW = 2     # page cards per row in the right-hand grid
DOCK_MAX = 4
DRAG_THRESHOLD = 8    # pixels before a press becomes a drag
ANIM_MS = 16

ALL_FILTER = "All"

# ---------- Default categories ----------
# Checked in this order; the first category whose keyword appears in the
# bundle ID or display name wins. Matching is case-insensitive substring.
CATEGORY_RULES = [
    ("Social", [
        "facebook", "instagram", "twitter", "tiktok", "snapchat", "reddit",
        "threads", "linkedin", "pinterest", "mastodon", "bereal",
    ]),
    ("Communication", [
        "messages", "mobilemail", "gmail", "outlook", "whatsapp", "messenger",
        "telegram", "discord", "slack", "zoom", "microsoftteams", "signal",
        "skype", "facetime", "mobilephone", "wechat",
    ]),
    ("Media & Entertainment", [
        "netflix", "youtube", "disney", "hulu", "twitch", "plex", "podcast",
        "kindle", "audible", "appletv", "primevideo",
    ]),
    ("Music", [
        "spotify", "music", "soundcloud", "pandora", "shazam", "deezer",
    ]),
    ("Photo & Video", [
        "photo", "camera", "lightroom", "capcut", "imovie", "vsco", "video",
    ]),
    ("Shopping & Food", [
        "amazon", "ebay", "etsy", "shop", "ubereats", "doordash", "deliveroo",
        "menulog", "starbucks", "mcdonald",
    ]),
    ("Travel & Maps", [
        "maps", "uber", "airbnb", "booking", "expedia", "tripadvisor",
        "trainline", "waze", "citymapper", "transit", "airline", "qantas",
        "jetstar", "virginaustralia", "tripit",
    ]),
    ("Finance", [
        "bank", "paypal", "wallet", "venmo", "coinbase", "stocks", "robinhood",
        "revolut", "monzo", "westpac", "commbank", "xero",
    ]),
    ("Health & Fitness", [
        "health", "fitness", "strava", "myfitnesspal", "calm", "headspace",
        "peloton", "garmin", "workout", "sleep",
    ]),
    ("Productivity", [
        "notes", "reminders", "calendar", "pages", "numbers", "keynote",
        "microsoft word", "excel", "powerpoint", "notion", "todoist", "trello",
        "asana", "dropbox", "drive", "onedrive", "files", "evernote", "documents",
        "sheets", "google docs",
    ]),
    ("Games", [
        "game", "roblox", "minecraft", "clash", "pokemon", "supercell",
        "playrix", "genshin", "fortnite",
    ]),
    ("Browsing", [
        "safari", "chrome", "firefox", "brave", "opera", "duckduckgo",
        "microsoftedge", "microsoft edge",
    ]),
    ("Utilities", [
        "calculator", "clock", "weather", "compass", "settings", "authenticator",
        "1password", "vpn", "flashlight", "translate", "measure", "magnifier",
        "shortcuts", "home",
    ]),
]

APPLE_CATEGORY = "Apple"
OTHER_CATEGORY = "Other"
CATEGORY_ORDER = [name for name, _ in CATEGORY_RULES] + [APPLE_CATEGORY, OTHER_CATEGORY]
CATEGORY_INDEX = {name: i for i, name in enumerate(CATEGORY_ORDER)}


def categorise(bundle_id, display_name):
    """Return the default category for an app based on its bundle ID and name."""
    text = f"{bundle_id} {display_name}".lower()
    for category, keywords in CATEGORY_RULES:
        if any(k in text for k in keywords):
            return category
    if bundle_id.lower().startswith("com.apple."):
        return APPLE_CATEGORY
    return OTHER_CATEGORY


def _all_widgets(widget):
    """Yield a widget and all of its descendants."""
    yield widget
    for child in widget.winfo_children():
        yield from _all_widgets(child)


class HomeScreenDragEditor:
    def __init__(self, root):
        self.root = root
        self.root.title("Home Screen Drag Organizer")
        self.root.geometry("1500x900")
        self.root.configure(bg=BG)

        self.raw_state = None
        self.all_apps = {}
        self.pil_icons = {}            # bundle_id -> PIL image (from iPhone)
        self.photo_cache = {}          # (bundle_id, size) -> PhotoImage
        self.placeholder_cache = {}    # bundle_id -> PIL image
        self.redraw_pending = False
        self.drag = None               # state of the current mouse drag
        self.folder_win = None         # open folder window
        self.overlay_folder = None
        self.overlay_grid = None
        self.category_var = tk.StringVar(value=ALL_FILTER)

        self._setup_styles()
        self._build_ui()

        self.root.bind_all("<MouseWheel>", self._on_wheel)
        self.root.bind_all("<Button-4>", self._on_wheel)
        self.root.bind_all("<Button-5>", self._on_wheel)

    # ---------- Styles ----------
    def _setup_styles(self):
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("TLabel", background=BG, foreground=FG)
        style.configure("TFrame", background=BG)
        style.configure("Primary.TButton", background="#2d5a9e", foreground="white",
                        font=("Helvetica", 10, "bold"), padding=6)
        style.map("Primary.TButton",
                  background=[("active", "#3a6fb8"), ("pressed", "#1e3f6e")])
        style.configure("Danger.TButton", background="#b03030", foreground="white",
                        font=("Helvetica", 10, "bold"), padding=6)
        style.map("Danger.TButton",
                  background=[("active", "#d04040"), ("pressed", "#802020")])
        style.configure("Neutral.TButton", background="#3a3a3a", foreground=FG,
                        font=("Helvetica", 10), padding=6)
        style.map("Neutral.TButton",
                  background=[("active", "#4a4a4a"), ("pressed", "#2a2a2a")])
        style.configure("Dark.TCombobox", fieldbackground=ENTRY_BG, background="#3a3a3a",
                        foreground=FG, arrowcolor=FG, bordercolor="#444444")
        style.map("Dark.TCombobox",
                  fieldbackground=[("readonly", ENTRY_BG)],
                  foreground=[("readonly", FG)],
                  selectbackground=[("readonly", ENTRY_BG)],
                  selectforeground=[("readonly", FG)])
        self.root.option_add("*TCombobox*Listbox.background", ENTRY_BG)
        self.root.option_add("*TCombobox*Listbox.foreground", FG)

    # ---------- UI ----------
    def _build_ui(self):
        # ---- Top bar ----
        topbar = tk.Frame(self.root, bg=BG)
        topbar.pack(fill=tk.X, padx=10, pady=8)

        ttk.Button(topbar, text="Connect & Read Layout", command=self.read_layout,
                   style="Primary.TButton").pack(side=tk.LEFT, padx=4)
        ttk.Button(topbar, text="Bulk Create Folders", command=self.bulk_create_folders,
                   style="Neutral.TButton").pack(side=tk.LEFT, padx=4)
        ttk.Button(topbar, text="Save Backup JSON", command=self.save_backup,
                   style="Neutral.TButton").pack(side=tk.LEFT, padx=4)
        ttk.Button(topbar, text="APPLY TO IPHONE", command=self.apply_changes,
                   style="Danger.TButton").pack(side=tk.LEFT, padx=4)

        self.status = tk.Label(topbar, text="Not connected", bg=BG, fg="#aaaaaa", anchor="w")
        self.status.pack(side=tk.LEFT, padx=16, fill=tk.X, expand=True)

        # ---- Main split ----
        pane = tk.PanedWindow(self.root, orient=tk.HORIZONTAL, bg=BG, sashwidth=4)
        pane.pack(fill=tk.BOTH, expand=True, padx=10, pady=4)

        # ===== LEFT: app library (drag from here) =====
        left = tk.Frame(pane, bg=BG)
        tk.Label(left, text="Apps (drag onto a page, folder or the dock)",
                 bg=BG, fg=FG, font=("Helvetica", 12, "bold")).pack(anchor="w")

        filter_row = tk.Frame(left, bg=BG)
        filter_row.pack(fill=tk.X, pady=4)

        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *a: self._rebuild_all())
        tk.Entry(filter_row, textvariable=self.search_var, bg=ENTRY_BG, fg=FG,
                 insertbackground=FG, relief=tk.FLAT, font=("Helvetica", 11)).pack(
            side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6), ipady=3)

        category_box = ttk.Combobox(filter_row, textvariable=self.category_var,
                                    values=[ALL_FILTER] + CATEGORY_ORDER,
                                    state="readonly", width=20, style="Dark.TCombobox")
        category_box.pack(side=tk.RIGHT)
        category_box.bind("<<ComboboxSelected>>", lambda e: self._rebuild_all())

        canvas_frame = tk.Frame(left, bg=BG)
        canvas_frame.pack(fill=tk.BOTH, expand=True)
        self.left_canvas = tk.Canvas(canvas_frame, bg=BG, highlightthickness=0)
        sb = tk.Scrollbar(canvas_frame, orient="vertical", command=self.left_canvas.yview)
        self.left_canvas.configure(yscrollcommand=sb.set)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.left_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.source_frame = tk.Frame(self.left_canvas, bg=BG)
        self.left_canvas.create_window((0, 0), window=self.source_frame, anchor="nw")
        self.source_frame.bind("<Configure>",
            lambda e: self.left_canvas.configure(scrollregion=self.left_canvas.bbox("all")))
        pane.add(left, width=340)

        # ===== RIGHT: dock + page grid =====
        right = tk.Frame(pane, bg=BG)
        tk.Label(right, text="Home Screen (drop an app on an app to make a folder)",
                 bg=BG, fg=FG, font=("Helvetica", 12, "bold")).pack(anchor="w")

        self.right_canvas = tk.Canvas(right, bg=BG, highlightthickness=0)
        right_sb = tk.Scrollbar(right, orient="vertical", command=self.right_canvas.yview)
        self.right_canvas.configure(yscrollcommand=right_sb.set)
        right_sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.right_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.targets_frame = tk.Frame(self.right_canvas, bg=BG)
        self.right_canvas.create_window((0, 0), window=self.targets_frame, anchor="nw")
        self.targets_frame.bind("<Configure>",
            lambda e: self.right_canvas.configure(scrollregion=self.right_canvas.bbox("all")))
        pane.add(right)

    # ---------- Async helper ----------
    def _run_async(self, coro, on_done):
        def worker():
            try:
                result = asyncio.run(coro)
            except Exception as e:
                result = e
            self.root.after(0, lambda: on_done(result))
        threading.Thread(target=worker, daemon=True).start()

    # ---------- Read layout & icons ----------
    def read_layout(self):
        self.status.config(text="Connecting…")

        async def _read():
            async with await create_using_usbmux() as lock:
                async with SpringBoardServicesService(lockdown=lock) as sb:
                    return await sb.get_icon_state()

        def done(result):
            if isinstance(result, Exception):
                messagebox.showerror("Read failed", str(result))
                self.status.config(text="Read failed")
                return
            self.raw_state = result
            self._build_app_index()
            self._rebuild_all()
            self._load_icons()

        self._run_async(_read(), done)

    def _build_app_index(self):
        self.all_apps.clear()

        def walk(obj):
            if isinstance(obj, dict):
                if "bundleIdentifier" in obj and "displayName" in obj and "elementType" not in obj:
                    self.all_apps[obj["bundleIdentifier"]] = obj
                for v in obj.values():
                    walk(v)
            elif isinstance(obj, list):
                for v in obj:
                    walk(v)

        walk(self.raw_state)

    def _load_icons(self):
        """Fetch every icon once, over a single connection, in a background thread."""
        bids = list(self.all_apps.keys())
        total = len(bids)
        if not total:
            return
        self.status.config(text=f"Loading icons 0/{total}…")

        def worker():
            count = 0

            async def _fetch_all():
                nonlocal count
                async with await create_using_usbmux() as lock:
                    async with SpringBoardServicesService(lockdown=lock) as sb:
                        for bid in bids:
                            img = None
                            try:
                                png = await sb.get_icon_pngdata(bid)
                                if png:
                                    img = Image.open(io.BytesIO(png)).convert("RGBA")
                            except Exception:
                                img = None
                            count += 1
                            self.root.after(0, self._icon_ready, bid, img, count, total)

            try:
                asyncio.run(_fetch_all())
            except Exception as e:
                self.root.after(0, lambda: self.status.config(text=f"Icon load failed: {e}"))
            else:
                self.root.after(0, lambda: self.status.config(
                    text=f"Loaded {total} apps / {len(self.raw_state)} pages"))

        threading.Thread(target=worker, daemon=True).start()

    def _icon_ready(self, bid, img, count, total):
        if img is not None:
            self.pil_icons[bid] = img
        for key in [k for k in self.photo_cache if k[0] == bid]:
            del self.photo_cache[key]
        self.status.config(text=f"Loading icons {count}/{total}…")
        if not self.redraw_pending:
            self.redraw_pending = True
            self.root.after(400, self._flush_redraw)

    def _flush_redraw(self):
        self.redraw_pending = False
        self._rebuild_all()

    # ---------- Images ----------
    def _placeholder(self, bid):
        if bid in self.placeholder_cache:
            return self.placeholder_cache[bid]
        name = self.all_apps.get(bid, {}).get("displayName", "?")
        palette = ["#4a7bd0", "#c0605a", "#5aa87a", "#b08a3e",
                   "#8a5ac0", "#3e9aa8", "#c05a95"]
        color = palette[sum(map(ord, bid)) % len(palette)]
        img = Image.new("RGBA", (256, 256), color)
        draw = ImageDraw.Draw(img)
        ch = (name.strip()[:1] or "?").upper()
        try:
            font = ImageFont.load_default(size=140)
        except TypeError:
            font = ImageFont.load_default()
        bbox = draw.textbbox((0, 0), ch, font=font)
        w, h = bbox[2] - bbox[0], bbox[3] - bbox[1]
        draw.text(((256 - w) / 2 - bbox[0], (256 - h) / 2 - bbox[1]), ch,
                  fill="white", font=font)
        self.placeholder_cache[bid] = img
        return img

    def _photo(self, bid, size):
        key = (bid, size)
        photo = self.photo_cache.get(key)
        if photo is not None:
            return photo
        src = self.pil_icons.get(bid) or self._placeholder(bid)
        img = src.convert("RGBA").resize((size, size), Image.LANCZOS)
        mask = Image.new("L", (size, size), 0)
        ImageDraw.Draw(mask).rounded_rectangle((0, 0, size - 1, size - 1),
                                               radius=max(4, size // 4), fill=255)
        img.putalpha(mask)
        photo = ImageTk.PhotoImage(img)
        self.photo_cache[key] = photo
        return photo

    # ---------- Widget builders ----------
    def _bind_press(self, widget, payload):
        """Make a widget (and its children) start a press/drag with this payload."""
        for w in _all_widgets(widget):
            w.bind("<ButtonPress-1>", lambda e, p=payload, o=widget: self._press(e, p, o))
            w.bind("<B1-Motion>", self._motion)
            w.bind("<ButtonRelease-1>", self._release)

    def _app_tile(self, parent, bid, size, label=True, drop=None):
        name = self.all_apps.get(bid, {}).get("displayName", bid)
        tile = tk.Frame(parent, bg=CARD_BG, highlightthickness=2,
                        highlightbackground=CARD_BG, cursor="hand2")
        tile._base_hl = CARD_BG
        img_lbl = tk.Label(tile, image=self._photo(bid, size), bg=CARD_BG)
        img_lbl.image = self._photo(bid, size)
        img_lbl.pack(padx=6, pady=(6, 2))
        if label:
            tk.Label(tile, text=name, bg=CARD_BG, fg=FG, font=("Helvetica", 9),
                     wraplength=TILE_W - 16).pack(pady=(0, 6))
        if drop is not None:
            tile._drop_target = drop
        self._bind_press(tile, {"kind": "app", "bid": bid, "on_click": None})
        return tile

    def _widget_tile(self, parent):
        tile = tk.Frame(parent, bg="#1a1a1a", width=TILE_W, height=TILE_H)
        tile.pack_propagate(False)
        tk.Label(tile, text="Widget", bg="#1a1a1a", fg=MUTED).pack(expand=True)
        return tile

    def _folder_apps(self, folder):
        apps = []
        for page in folder.get("iconLists", []):
            if isinstance(page, list):
                for a in page:
                    if isinstance(a, dict) and "bundleIdentifier" in a:
                        apps.append(a)
        return apps

    def _folder_tile(self, parent, folder):
        name = folder.get("displayName", "Folder")
        apps = self._folder_apps(folder)

        tile = tk.Frame(parent, bg=FOLDER_BG, width=TILE_W, height=TILE_H,
                        highlightthickness=2, highlightbackground=FOLDER_BG, cursor="hand2")
        tile.pack_propagate(False)
        tile._base_hl = FOLDER_BG
        tile._drop_target = ("folder", folder)

        preview = tk.Frame(tile, bg=FOLDER_PREVIEW, padx=6, pady=6)
        preview.pack(pady=(8, 2))
        for i, a in enumerate(apps[:9]):
            photo = self._photo(a.get("bundleIdentifier", ""), ICON_MINI)
            lbl = tk.Label(preview, image=photo, bg=FOLDER_PREVIEW)
            lbl.image = photo
            lbl.grid(row=i // 3, column=i % 3, padx=2, pady=2)
        if not apps:
            tk.Label(preview, text="Empty", bg=FOLDER_PREVIEW, fg=MUTED,
                     font=("Helvetica", 8)).grid(row=0, column=0)

        tk.Label(tile, text=name, bg=FOLDER_BG, fg=FOLDER_NAME_FG,
                 font=("Helvetica", 9, "bold"), wraplength=TILE_W - 12).pack()

        self._bind_press(tile, {"kind": "folder", "bid": None,
                                "on_click": lambda f=folder: self._open_folder(f)})
        return tile

    def _dock_card(self, parent):
        card = tk.Frame(parent, bg=CARD_BG, highlightthickness=2,
                        highlightbackground=CARD_BG, padx=10, pady=8)
        card._base_hl = CARD_BG
        card._drop_target = ("dock",)

        tk.Label(card, text=f"Dock (max {DOCK_MAX})", bg=CARD_BG, fg=HEADER_FG,
                 font=("Helvetica", 11, "bold")).pack(anchor="w")
        row = tk.Frame(card, bg=CARD_BG)
        row.pack(pady=4)

        dock_apps = [a for a in self.raw_state[0]
                     if isinstance(a, dict) and "bundleIdentifier" in a
                     and a.get("elementType") != "widget"]
        for a in dock_apps:
            self._app_tile(row, a["bundleIdentifier"], ICON_TILE, label=False).pack(
                side=tk.LEFT, padx=4)
        if not dock_apps:
            tk.Label(row, text="Drop up to 4 apps here", bg=CARD_BG, fg=MUTED).pack(
                padx=20, pady=10)
        return card

    def _page_card(self, parent, idx):
        page = self.raw_state[idx] if isinstance(self.raw_state[idx], list) else []
        card = tk.Frame(parent, bg=CARD_BG, highlightthickness=2,
                        highlightbackground=CARD_BG, padx=10, pady=8)
        card._base_hl = CARD_BG
        card._drop_target = ("page", idx)

        tk.Label(card, text=f"Page {idx}", bg=CARD_BG, fg=HEADER_FG,
                 font=("Helvetica", 11, "bold")).pack(anchor="w")

        grid = tk.Frame(card, bg=CARD_BG)
        grid.pack(pady=(4, 0))

        items = [it for it in page if isinstance(it, dict)]
        if not items:
            tk.Label(grid, text="Drop apps here", bg=CARD_BG, fg=MUTED).grid(
                row=0, column=0, columnspan=COLS, pady=20)

        for i, it in enumerate(items):
            r, c = divmod(i, COLS)
            if it.get("listType") == "folder":
                tile = self._folder_tile(grid, it)
            elif it.get("elementType") == "widget":
                tile = self._widget_tile(grid)
            elif "bundleIdentifier" in it:
                tile = self._app_tile(grid, it["bundleIdentifier"], ICON_TILE,
                                      drop=("app", idx, it["bundleIdentifier"]))
            else:
                continue
            tile.grid(row=r, column=c, padx=4, pady=4)

        rows = max(MIN_ROWS, math.ceil(len(items) / COLS))
        for r in range(rows):
            grid.grid_rowconfigure(r, minsize=TILE_H + 8)
        for c in range(COLS):
            grid.grid_columnconfigure(c, minsize=TILE_W + 8)
        return card

    def _new_page_card(self, parent, idx):
        card = tk.Frame(parent, bg=CARD_BG, highlightthickness=2,
                        highlightbackground=CARD_BG, width=COLS * (TILE_W + 8) + 20,
                        height=260, cursor="hand2")
        card.pack_propagate(False)
        card._base_hl = CARD_BG
        card._drop_target = ("page", idx)
        tk.Label(card, text="+  New Page", bg=CARD_BG, fg=MUTED,
                 font=("Helvetica", 14, "bold")).pack(expand=True)
        self._bind_press(card, {"kind": "newpage", "bid": None, "on_click": self._add_page})
        return card

    # ---------- Rendering ----------
    def _rebuild_all(self):
        # Don't destroy widgets while a drag is in progress
        if self.drag and self.drag.get("active"):
            self.root.after(200, self._rebuild_all)
            return
        if self.raw_state is None:
            return
        self._refresh_source_list()
        self._rebuild_targets()
        self._refresh_overlay()

    def _sorted_visible_apps(self):
        query = self.search_var.get().lower()
        selected = self.category_var.get()

        visible = []
        for bid, app in self.all_apps.items():
            name = app.get("displayName", "")
            if query and query not in name.lower() and query not in bid.lower():
                continue
            category = categorise(bid, name)
            if selected != ALL_FILTER and category != selected:
                continue
            visible.append((category, bid, name))

        visible.sort(key=lambda x: (CATEGORY_INDEX[x[0]], x[2].lower()))
        return visible

    def _refresh_source_list(self):
        for w in self.source_frame.winfo_children():
            w.destroy()

        visible = self._sorted_visible_apps()
        show_headers = self.category_var.get() == ALL_FILTER
        current_category = None

        for category, bid, name in visible:
            if show_headers and category != current_category:
                current_category = category
                tk.Label(self.source_frame, text=category, bg=BG, fg=HEADER_FG,
                         font=("Helvetica", 11, "bold")).pack(anchor="w", pady=(12, 2))

            row = tk.Frame(self.source_frame, bg=BG, cursor="hand2")
            row.pack(fill=tk.X, pady=2, padx=4)

            icon = tk.Label(row, image=self._photo(bid, ICON_LIST), bg=BG)
            icon.image = self._photo(bid, ICON_LIST)
            icon.pack(side=tk.LEFT, padx=(4, 10), pady=2)
            tk.Label(row, text=name, bg=BG, fg=FG, font=("Helvetica", 12),
                     anchor="w").pack(side=tk.LEFT, fill=tk.X, expand=True)

            self._bind_press(row, {"kind": "app", "bid": bid, "on_click": None})

        if not visible:
            tk.Label(self.source_frame, text="No apps match this filter.",
                     bg=BG, fg=MUTED).pack(anchor="w", pady=8)

    def _rebuild_targets(self):
        for w in self.targets_frame.winfo_children():
            w.destroy()
        if not self.raw_state:
            return

        self._dock_card(self.targets_frame).pack(fill=tk.X, padx=6, pady=6)

        pages_grid = tk.Frame(self.targets_frame, bg=BG)
        pages_grid.pack(anchor="nw", padx=6)

        n = 0
        for idx in range(1, len(self.raw_state)):
            card = self._page_card(pages_grid, idx)
            card.grid(row=n // PAGES_PER_ROW, column=n % PAGES_PER_ROW,
                      padx=8, pady=8, sticky="n")
            n += 1

        new_card = self._new_page_card(pages_grid, len(self.raw_state))
        new_card.grid(row=n // PAGES_PER_ROW, column=n % PAGES_PER_ROW,
                      padx=8, pady=8, sticky="n")

    def _add_page(self):
        self.raw_state.append([])
        self._rebuild_all()

    # ---------- Mouse drag engine ----------
    def _press(self, e, payload, origin):
        self.drag = {
            "payload": payload,
            "origin": origin,
            "sx": e.x_root, "sy": e.y_root,
            "cur": (e.x_root, e.y_root),
            "moved": False,
            "active": False,
            "ghost": None,
            "gpos": None,
            "hover": None,
            "tick": None,
        }

    def _motion(self, e):
        d = self.drag
        if not d:
            return
        d["cur"] = (e.x_root, e.y_root)
        if not d["active"]:
            if abs(e.x_root - d["sx"]) + abs(e.y_root - d["sy"]) < DRAG_THRESHOLD:
                return
            d["moved"] = True
            if d["payload"].get("kind") != "app":
                return
            self._start_ghost(d)
        self._set_hover(d, self._hit_test(e.x_root, e.y_root))

    def _release(self, e):
        d = self.drag
        self.drag = None
        if not d:
            return

        if not d["active"]:
            on_click = d["payload"].get("on_click")
            if on_click and not d.get("moved"):
                on_click()
            return

        if d.get("tick"):
            self.root.after_cancel(d["tick"])
        self._set_hover(d, None)

        hit = self._hit_test(e.x_root, e.y_root)
        bid = d["payload"]["bid"]
        half = ICON_DRAG // 2
        if hit and self._can_drop(bid, hit[0]):
            w = hit[1]
            tx = w.winfo_rootx() + w.winfo_width() // 2 - half
            ty = w.winfo_rooty() + w.winfo_height() // 2 - half
            self._animate_ghost(d, tx, ty, fade=True,
                                done=lambda: self._finish_drop(d, hit[0]))
        else:
            self._animate_ghost(d, d["sx"] - half, d["sy"] - half, fade=False,
                                done=lambda: self._destroy_ghost(d))

    def _start_ghost(self, d):
        d["active"] = True
        bid = d["payload"]["bid"]
        name = self.all_apps.get(bid, {}).get("displayName", "")

        g = tk.Toplevel(self.root)
        g.overrideredirect(True)
        g.attributes("-topmost", True)
        try:
            g.attributes("-alpha", 0.92)
        except tk.TclError:
            pass
        g.configure(bg=GHOST_BG)

        photo = self._photo(bid, ICON_DRAG)
        icon = tk.Label(g, image=photo, bg=GHOST_BG)
        icon.image = photo
        icon.pack(padx=6, pady=(6, 0))
        tk.Label(g, text=name, bg=GHOST_BG, fg=FG,
                 font=("Helvetica", 9, "bold")).pack(padx=6, pady=(0, 6))

        d["ghost"] = g
        # Lift from the press point, then follow the cursor
        d["gpos"] = (float(d["sx"] - ICON_DRAG // 2), float(d["sy"] - ICON_DRAG // 2))
        g.geometry(f"+{int(d['gpos'][0])}+{int(d['gpos'][1])}")
        self._tick(d)

    def _tick(self, d):
        if not d.get("active") or d.get("ghost") is None:
            return
        cx, cy = d["cur"]
        tx, ty = cx + 14, cy + 14          # sit just below-right so the pointer is never covered
        gx, gy = d["gpos"]
        gx += (tx - gx) * 0.3              # ease toward the cursor
        gy += (ty - gy) * 0.3
        d["gpos"] = (gx, gy)
        try:
            d["ghost"].geometry(f"+{int(gx)}+{int(gy)}")
        except tk.TclError:
            return
        d["tick"] = self.root.after(ANIM_MS, self._tick, d)

    def _animate_ghost(self, d, tx, ty, fade, done, steps=12):
        sx, sy = d["gpos"]

        def step(i=0):
            g = d.get("ghost")
            if g is None:
                return
            t = (i + 1) / steps
            ease = t * t * (3 - 2 * t)      # smoothstep
            x = sx + (tx - sx) * ease
            y = sy + (ty - sy) * ease
            try:
                g.geometry(f"+{int(x)}+{int(y)}")
                if fade:
                    g.attributes("-alpha", max(0.05, 0.92 * (1 - ease)))
            except tk.TclError:
                return
            if i + 1 < steps:
                self.root.after(ANIM_MS, step, i + 1)
            else:
                done()

        step()

    def _destroy_ghost(self, d):
        g = d.get("ghost")
        if g is not None:
            try:
                g.destroy()
            except tk.TclError:
                pass
        d["ghost"] = None
        d["active"] = False

    def _finish_drop(self, d, target):
        self._destroy_ghost(d)
        bid = d["payload"]["bid"]
        self._move_app(bid, target)
        self._prune_empty_folders()
        self._rebuild_all()

    def _set_hover(self, d, hit):
        old = d.get("hover")
        new = hit[1] if hit else None
        if old is new:
            return
        if old is not None:
            try:
                old.config(highlightbackground=getattr(old, "_base_hl", CARD_BG))
            except tk.TclError:
                pass
        if new is not None:
            try:
                new.config(highlightbackground=HIGHLIGHT)
            except tk.TclError:
                new = None
        d["hover"] = new

    def _hit_test(self, x, y):
        """Find the nearest drop target under the pointer, as (target, widget)."""
        w = self.root.winfo_containing(x, y)
        while w is not None:
            target = getattr(w, "_drop_target", None)
            if target is not None:
                return (target, w)
            w = w.master
        return None

    def _can_drop(self, bid, target):
        kind = target[0]
        if kind == "app":
            return target[2] != bid
        if kind == "dock":
            others = [a for a in self.raw_state[0]
                      if isinstance(a, dict) and a.get("bundleIdentifier") != bid
                      and a.get("elementType") != "widget"]
            if len(others) >= DOCK_MAX:
                self.status.config(text=f"Dock is full ({DOCK_MAX} apps)")
                return False
        return True

    # ---------- Layout changes ----------
    def _read_app_name(self, bid):
        return self.all_apps.get(bid, {}).get("displayName", bid)

    def _move_app(self, bid, target):
        app = self.all_apps.get(bid)
        if app is None:
            return
        name = self._read_app_name(bid)
        kind = target[0]

        self._remove_app_from_layout(bid)

        if kind == "folder":
            folder = target[1]
            inner = folder.get("iconLists")
            if not inner:
                inner = [[]]
                folder["iconLists"] = inner
            inner[0].append(app)
            msg = f"Moved {name} → {folder.get('displayName', 'folder')}"

        elif kind == "dock":
            self.raw_state[0].append(app)
            msg = f"Moved {name} → Dock"

        elif kind == "page":
            idx = target[1]
            while len(self.raw_state) <= idx:
                self.raw_state.append([])
            self.raw_state[idx].append(app)
            msg = f"Moved {name} → Page {idx}"

        elif kind == "app":
            idx, target_bid = target[1], target[2]
            page = self.raw_state[idx]
            for i, it in enumerate(page):
                if (isinstance(it, dict) and it.get("bundleIdentifier") == target_bid
                        and it.get("listType") != "folder"
                        and it.get("elementType") != "widget"):
                    page[i] = {"listType": "folder", "displayName": "New Folder",
                               "iconLists": [[it, app]]}
                    break
            else:
                page.append(app)
            msg = f"Created folder with {name} and {self._read_app_name(target_bid)}"
        else:
            return

        self.status.config(text=msg)

    def _remove_app_from_layout(self, bundle_id):
        def strip(lst):
            out = []
            for item in lst:
                if isinstance(item, dict):
                    if item.get("bundleIdentifier") == bundle_id and item.get("elementType") != "widget":
                        continue
                    if item.get("listType") == "folder":
                        inner = item.get("iconLists", [])
                        item["iconLists"] = [strip(p) for p in inner]
                out.append(item)
            return out

        for i in range(len(self.raw_state)):
            self.raw_state[i] = strip(self.raw_state[i])

    def _prune_empty_folders(self):
        def prune(lst):
            out = []
            for it in lst:
                if (isinstance(it, dict) and it.get("listType") == "folder"
                        and not self._folder_apps(it)):
                    continue
                out.append(it)
            return out

        for i in range(len(self.raw_state)):
            if isinstance(self.raw_state[i], list):
                self.raw_state[i] = prune(self.raw_state[i])

    # ---------- Folder window ----------
    def _folder_in_layout(self, folder):
        return any(it is folder
                   for page in self.raw_state if isinstance(page, list)
                   for it in page)

    def _open_folder(self, folder):
        if not self._folder_in_layout(folder):
            return
        self._close_folder_window()

        name = folder.get("displayName", "Folder")
        win = tk.Toplevel(self.root)
        win.title(name)
        win.configure(bg=BG)
        win.transient(self.root)
        win.protocol("WM_DELETE_WINDOW", self._close_folder_window)

        tk.Label(win, text=name, bg=BG, fg=FOLDER_NAME_FG,
                 font=("Helvetica", 16, "bold")).pack(pady=(14, 4), padx=20)

        grid = tk.Frame(win, bg=FOLDER_BG, padx=14, pady=14,
                        highlightthickness=2, highlightbackground=FOLDER_BG)
        grid.pack(padx=20, pady=6)
        grid._base_hl = FOLDER_BG
        grid._drop_target = ("folder", folder)

        ttk.Button(win, text="Close", style="Neutral.TButton",
                   command=self._close_folder_window).pack(pady=(4, 14))

        self.folder_win = win
        self.overlay_folder = folder
        self.overlay_grid = grid
        self._fill_overlay()

    def _fill_overlay(self):
        if self.overlay_grid is None:
            return
        for w in self.overlay_grid.winfo_children():
            w.destroy()

        apps = self._folder_apps(self.overlay_folder)
        if not apps:
            tk.Label(self.overlay_grid, text="Drag apps here", bg=FOLDER_BG, fg=MUTED,
                     font=("Helvetica", 11)).grid(row=0, column=0, padx=40, pady=40)
            return

        for i, a in enumerate(apps):
            tile = self._app_tile(self.overlay_grid, a["bundleIdentifier"], ICON_OVERLAY)
            tile.grid(row=i // COLS, column=i % COLS, padx=8, pady=8)

    def _refresh_overlay(self):
        if self.folder_win is None:
            return
        if not self._folder_in_layout(self.overlay_folder):
            self._close_folder_window()
            return
        self._fill_overlay()

    def _close_folder_window(self):
        if self.folder_win is not None:
            try:
                self.folder_win.destroy()
            except tk.TclError:
                pass
        self.folder_win = None
        self.overlay_folder = None
        self.overlay_grid = None

    # ---------- Mouse wheel scrolling ----------
    def _on_wheel(self, e):
        w = self.root.winfo_containing(e.x_root, e.y_root)
        canvas = None
        while w is not None:
            if w is self.left_canvas or w is self.right_canvas:
                canvas = w
                break
            w = w.master
        if canvas is None:
            return
        if getattr(e, "num", None) == 4:
            direction = -1
        elif getattr(e, "num", None) == 5:
            direction = 1
        else:
            direction = -1 if getattr(e, "delta", 0) > 0 else 1
        canvas.yview_scroll(direction, "units")

    # ---------- Bulk folder creation ----------
    def bulk_create_folders(self):
        if not self.raw_state:
            messagebox.showwarning("Not loaded", "Connect and read the layout first.")
            return

        text = simpledialog.askstring(
            "Bulk Create Folders",
            "Enter folder names, one per line:",
            parent=self.root
        )
        if not text:
            return

        names = [n.strip() for n in text.splitlines() if n.strip()]
        if not names:
            return

        page_idx = simpledialog.askinteger(
            "Target Page",
            f"Which page should the folders go on? (1 to {len(self.raw_state) - 1})",
            parent=self.root, minvalue=1, maxvalue=len(self.raw_state) - 1
        )
        if page_idx is None:
            return

        while len(self.raw_state) <= page_idx:
            self.raw_state.append([])

        created = 0
        for name in names:
            exists = any(isinstance(it, dict) and it.get("listType") == "folder"
                         and it.get("displayName") == name
                         for it in self.raw_state[page_idx])
            if exists:
                continue
            folder = {"iconLists": [[]], "listType": "folder", "displayName": name}
            self.raw_state[page_idx].append(folder)
            created += 1

        self._rebuild_all()
        self.status.config(text=f"Created {created} folders on Page {page_idx}")

    # ---------- Backup & Apply ----------
    def _write_backup_file(self):
        if not self.raw_state:
            return None
        ts = datetime.now().strftime("%Y-%m-%d_%H%M%S")
        path = f"homescreen_backup_{ts}.json"

        def default(o):
            if isinstance(o, datetime):
                return o.replace(microsecond=0).isoformat()
            raise TypeError

        with open(path, "w") as f:
            json.dump(self.raw_state, f, indent=2, default=default)
        self.backup_path = path
        return path

    def save_backup(self):
        path = self._write_backup_file()
        if path:
            messagebox.showinfo("Backup saved", f"Saved to:\n{os.path.abspath(path)}")
        else:
            messagebox.showwarning("No layout", "Read a layout first.")

    def apply_changes(self):
        if not self.raw_state:
            return
        if not messagebox.askyesno("Confirm", "Overwrite Home Screen on iPhone?"):
            return

        backup_path = self._write_backup_file()
        if not backup_path:
            messagebox.showerror("Backup failed", "Could not save backup. Aborting.")
            return
        self.status.config(text=f"Backup saved: {backup_path}. Writing…")

        def clean(o):
            if isinstance(o, datetime):
                return o.replace(microsecond=0)
            if isinstance(o, list):
                return [clean(x) for x in o]
            if isinstance(o, dict):
                return {k: clean(v) for k, v in o.items()}
            return o

        payload = clean(self.raw_state)

        async def _write():
            async with await create_using_usbmux() as lock:
                async with SpringBoardServicesService(lockdown=lock) as sb:
                    await sb.set_icon_state(payload)

        def done(result):
            if isinstance(result, Exception):
                messagebox.showerror("Write failed", str(result))
                self.status.config(text=f"Write failed: {result}")
            else:
                messagebox.showinfo("Sent", "Check your iPhone.")
                self.status.config(text="Write sent")

        self._run_async(_write(), done)


if __name__ == "__main__":
    root = tk.Tk()
    HomeScreenDragEditor(root)
    root.mainloop()