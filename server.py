import asyncio
import json
import os
import re
import threading
import time
from datetime import datetime

import uvicorn
from fastapi import FastAPI, HTTPException
from fastapi.responses import FileResponse
from pydantic import BaseModel
from pymobiledevice3.lockdown import create_using_usbmux
from pymobiledevice3.services.springboard import SpringBoardServicesService

BASE = os.path.dirname(os.path.abspath(__file__))
ICON_DIR = os.path.join(BASE, "icon_cache")
os.makedirs(ICON_DIR, exist_ok=True)
PORT = 8765

app = FastAPI()
device_lock = asyncio.Lock()
STATE = {"layout": None, "apps": {}, "prefetching": False}


async def with_springboard(fn):
    """Run fn(springboard) on one device connection, one operation at a time."""
    async with device_lock:
        async with await create_using_usbmux() as lock:
            async with SpringBoardServicesService(lockdown=lock) as sb:
                return await fn(sb)


def icon_path(bid):
    safe = re.sub(r"[^A-Za-z0-9._-]", "_", bid)
    return os.path.join(ICON_DIR, safe + ".png")


def index_apps(obj, out):
    if isinstance(obj, dict):
        if "bundleIdentifier" in obj and "displayName" in obj and "elementType" not in obj:
            out[obj["bundleIdentifier"]] = obj
        for v in obj.values():
            index_apps(v, out)
    elif isinstance(obj, list):
        for v in obj:
            index_apps(v, out)


async def prefetch_icons(bids):
    """Fetch all icons once over a single connection and cache them on disk."""
    if STATE["prefetching"]:
        return
    STATE["prefetching"] = True
    try:
        async with device_lock:
            async with await create_using_usbmux() as lock:
                async with SpringBoardServicesService(lockdown=lock) as sb:
                    for bid in bids:
                        path = icon_path(bid)
                        if os.path.exists(path):
                            continue
                        try:
                            png = await sb.get_icon_pngdata(bid)
                        except Exception:
                            png = None
                        if png:
                            with open(path, "wb") as f:
                                f.write(png)
    finally:
        STATE["prefetching"] = False


def clean(o):
    if isinstance(o, datetime):
        return o.replace(microsecond=0)
    if isinstance(o, list):
        return [clean(x) for x in o]
    if isinstance(o, dict):
        return {k: clean(v) for k, v in o.items()}
    return o


def restore(obj, originals):
    """Swap app entries back to the untouched originals from the iPhone so no fields are lost."""
    if isinstance(obj, list):
        return [restore(x, originals) for x in obj]
    if isinstance(obj, dict):
        if obj.get("listType") == "folder":
            new = {k: v for k, v in obj.items() if k != "id"}
            new["iconLists"] = [restore(p, originals) for p in obj.get("iconLists", [])]
            return new
        bid = obj.get("bundleIdentifier")
        if bid and obj.get("elementType") != "widget" and bid in originals:
            return originals[bid]
    return obj


def write_backup(layout):
    ts = datetime.now().strftime("%Y-%m-%d_%H%M%S")
    path = os.path.join(BASE, f"homescreen_backup_{ts}.json")
    with open(path, "w", encoding="utf-8") as f:
        json.dump(layout, f, indent=2,
                  default=lambda o: o.isoformat() if isinstance(o, datetime) else str(o))
    return path


class LayoutIn(BaseModel):
    layout: list


@app.post("/api/read")
async def read_layout():
    try:
        layout = await with_springboard(lambda sb: sb.get_icon_state())
    except Exception as e:
        raise HTTPException(500, f"Read failed: {e}")
    apps = {}
    index_apps(layout, apps)
    STATE["layout"], STATE["apps"] = layout, apps
    asyncio.create_task(prefetch_icons(list(apps.keys())))
    return {"layout": layout,
            "apps": {bid: a.get("displayName", bid) for bid, a in apps.items()}}


@app.get("/api/status")
def status():
    return {"loaded": STATE["layout"] is not None,
            "apps": len(STATE["apps"]),
            "icons_cached": len(os.listdir(ICON_DIR)),
            "prefetching": STATE["prefetching"]}


@app.get("/api/icon/{bid}")
def icon(bid: str):
    path = icon_path(bid)
    if not os.path.exists(path):
        raise HTTPException(404, "No icon yet")
    return FileResponse(path, media_type="image/png")


@app.post("/api/backup")
def backup():
    if STATE["layout"] is None:
        raise HTTPException(400, "Read the layout first")
    return {"path": write_backup(STATE["layout"])}


@app.put("/api/layout")
async def apply_layout(body: LayoutIn):
    if STATE["layout"] is None:
        raise HTTPException(400, "Read the layout first")
    backup_path = write_backup(STATE["layout"])
    payload = clean(restore(body.layout, STATE["apps"]))
    try:
        await with_springboard(lambda sb: sb.set_icon_state(payload))
    except Exception as e:
        raise HTTPException(500, f"Write failed: {e}")
    STATE["layout"] = payload
    return {"ok": True, "backup": backup_path}


@app.get("/")
def index():
    return FileResponse(os.path.join(BASE, "index.html"))


def run_server():
    uvicorn.run(app, host="127.0.0.1", port=PORT, log_level="warning")


if __name__ == "__main__":
    threading.Thread(target=run_server, daemon=True).start()
    time.sleep(1.0)
    import webview
    webview.create_window("Home Screen Organizer", f"http://127.0.0.1:{PORT}",
                          width=1500, height=900)
    webview.start()