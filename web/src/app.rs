use crate::{
    help::Help,
    settings::Settings,
    worker::{Request, Response, Worker},
    world::World,
};
use js_sys::Array;
use rlifesrc_lib::{Config, Status};
use std::time::Duration;
use wasm_bindgen::JsValue;
use web_sys::{Blob, BlobPropertyBag, FileList, HtmlAnchorElement, HtmlElement, Url};
use yew::{
    events::WheelEvent,
    format::{Json, Text},
    html,
    html::ChangeData,
    services::{
        interval::{IntervalService, IntervalTask},
        reader::{FileData, ReaderService, ReaderTask},
        DialogService,
    },
    Bridge, Bridged, Component, ComponentLink, Html, ShouldRender,
};

const INIT_WORLD: &str = "x = 16, y = 16, rule = B3/S23\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????$\n\
                          ????????????????!";

pub struct App {
    link: ComponentLink<Self>,
    config: Config,
    status: Status,
    gen: isize,
    cells: usize,
    world: String,
    max_partial: bool,
    worker: Box<dyn Bridge<Worker>>,
    interval_task: Option<IntervalTask>,
    reader_task: Option<ReaderTask>,
}

pub enum Msg {
    Tick,
    IncGen,
    DecGen,
    Start,
    Pause,
    Reset,
    Save,
    Load(FileList),
    SendFile(FileData),
    SetMaxPartial,
    Apply(Config),
    DataReceived(Response),
    None,
}

impl App {
    fn start_job(&mut self) {
        let handle = IntervalService::spawn(
            Duration::from_millis(1000 / 60),
            self.link.callback(|_| Msg::Tick),
        );
        self.interval_task = Some(handle);
    }

    fn stop_job(&mut self) {
        self.interval_task.take();
    }
}

impl Component for App {
    type Message = Msg;
    type Properties = ();

    fn create(_: Self::Properties, link: ComponentLink<Self>) -> Self {
        let config: Config = Config::default();
        let status = Status::Initial;
        let world = INIT_WORLD.to_owned();
        let callback = link.callback(Msg::DataReceived);
        let worker = Worker::bridge(callback);

        App {
            link,
            config,
            status,
            gen: 0,
            cells: 0,
            world,
            max_partial: false,
            worker,
            interval_task: None,
            reader_task: None,
        }
    }

    fn update(&mut self, msg: Self::Message) -> ShouldRender {
        match msg {
            Msg::Tick => {
                if self.max_partial {
                    self.worker.send(Request::MaxPartial)
                } else {
                    self.worker.send(Request::DisplayGen(self.gen))
                }
            }
            Msg::IncGen => {
                if self.gen < self.config.period - 1 {
                    self.gen += 1;
                    self.worker.send(Request::DisplayGen(self.gen));
                    return true;
                }
            }
            Msg::DecGen => {
                if self.gen > 0 {
                    self.gen -= 1;
                    self.worker.send(Request::DisplayGen(self.gen));
                    return true;
                }
            }
            Msg::Start => self.worker.send(Request::Start),
            Msg::Pause => self.worker.send(Request::Pause),
            Msg::Reset => self.worker.send(Request::SetWorld(self.config.clone())),
            Msg::Save => self.worker.send(Request::Save),
            Msg::Load(files) => {
                let file = files.get(0).unwrap();
                let mut reader_service = ReaderService::new();
                let task = reader_service
                    .read_file(file, self.link.callback(Msg::SendFile))
                    .unwrap();
                self.reader_task = Some(task)
            }
            Msg::SendFile(data) => {
                if let Json(Ok(world_ser)) = Ok(data.content).into() {
                    self.worker.send(Request::Load(world_ser));
                } else {
                    DialogService::alert("Broken saved file.");
                }
            }
            Msg::SetMaxPartial => {
                self.max_partial ^= true;
                if self.max_partial {
                    self.worker.send(Request::MaxPartial)
                } else {
                    self.worker.send(Request::DisplayGen(self.gen))
                }
                return true;
            }
            Msg::Apply(config) => {
                self.config = config;
                self.gen = 0;
                self.worker.send(Request::SetWorld(self.config.clone()));
                return true;
            }
            Msg::DataReceived(response) => {
                match response {
                    Response::UpdateWorld((world, cells)) => {
                        self.world = world;
                        self.cells = cells;
                    }
                    Response::UpdateConfig(config) => {
                        self.config = config;
                    }
                    Response::UpdateStatus(status) => {
                        let old_status = self.status;
                        if self.status != status {
                            match (old_status, status) {
                                (Status::Searching, _) => self.stop_job(),
                                (_, Status::Searching) => self.start_job(),
                                _ => (),
                            }
                            self.status = status;
                        }
                    }
                    Response::Error(error) => {
                        DialogService::alert(&error);
                    }
                    Response::Save(world_ser) => {
                        let text: Text = Json(&world_ser).into();
                        download(&text.unwrap(), "save.json", "application/json").unwrap();
                    }
                };
                return true;
            }
            Msg::None => (),
        }
        false
    }

    fn change(&mut self, _: Self::Properties) -> ShouldRender {
        false
    }

    fn view(&self) -> Html {
        html! {
            <div id="rlifesrc">
                { self.header() }
                { self.main() }
                { self.footer() }
            </div>
        }
    }
}

impl App {
    fn header(&self) -> Html {
        html! {
            <header id="appbar" class="mui-appbar mui--z1">
                <table class="mui-container-fluid">
                    <tr class="mui--appbar-height">
                        <td>
                            <span id="title" class="mui--text-headline">
                                { "Rust Life Search" }
                            </span>
                            <span class="mui--text-subhead mui--hidden-xs">
                                { "A Game of Life pattern searcher written in Rust." }
                            </span>
                        </td>
                        <td class="mui--text-right">
                            <a href="https://github.com/AlephAlpha/rlifesrc/"
                                class="mui--text-headline">
                                <i class="fab fa-github"></i>
                            </a>
                        </td>
                    </tr>
                </table>
            </header>
        }
    }

    fn footer(&self) -> Html {
        html! {
            <footer id="footer" class="mui-container-fluid">
                <div class="mui--text-caption mui--text-center">
                    { "Powered by " }
                    <a href="https://yew.rs">
                        { "Yew" }
                    </a>
                    { " & " }
                    <a href="https://www.muicss.com">
                        { "MUI CSS" }
                    </a>
                </div>
            </footer>
        }
    }

    fn main(&self) -> Html {
        html! {
            <main class="mui-container-fluid">
                <div class="mui-row">
                    <div class="mui-col-sm-10 mui-col-sm-offset-1 mui-col-lg-8 mui-col-lg-offset-2">
                        <div class="mui-panel">
                            <ul class="mui-tabs__bar">
                                <li class="mui--is-active">
                                    <a data-mui-toggle="tab" data-mui-controls="pane-world">
                                        <i class="fas fa-globe"></i>
                                        <span class="mui--hidden-xs"> { "World" } </span>
                                    </a>
                                </li>
                                <li>
                                    <a data-mui-toggle="tab" data-mui-controls="pane-settings">
                                        <i class="fas fa-cog"></i>
                                        <span class="mui--hidden-xs"> { "Settings" } </span>
                                    </a>
                                </li>
                                <li>
                                    <a data-mui-toggle="tab" data-mui-controls="pane-help">
                                        <i class="fas fa-question-circle"></i>
                                        <span class="mui--hidden-xs"> { "Help" } </span>
                                    </a>
                                </li>
                            </ul>
                            <div class="mui-tabs__pane mui--is-active" id="pane-world">
                                { self.data() }
                                <div class="mui-checkbox">
                                    <label>
                                        <input id="partial-max"
                                            type="checkbox"
                                            checked=self.max_partial
                                            onclick=self.link.callback(|_| Msg::SetMaxPartial)/>
                                        <abbr title="Show maximal partial result.">
                                            { "Max Partial" }
                                        </abbr>
                                    </label>
                                </div>
                                <World world=&self.world/>
                                { self.buttons() }
                            </div>
                            <div class="mui-tabs__pane" id="pane-settings">
                                <Settings config=&self.config
                                    callback=self.link.callback(Msg::Apply)/>
                            </div>
                            <div class="mui-tabs__pane" id="pane-help">
                                <Help/>
                            </div>
                        </div>
                    </div>
                </div>
            </main>
        }
    }

    fn data(&self) -> Html {
        let onwheel = self.link.callback(|e: WheelEvent| {
            e.prevent_default();
            if e.delta_y() < 0.0 {
                Msg::IncGen
            } else {
                Msg::DecGen
            }
        });
        html! {
            <ul id="data" class="mui-list--inline mui--text-body2">
                <li onwheel=onwheel
                    class=if self.max_partial { "mui--hide" } else { "" }>
                    <abbr title="The displayed generation.">
                        { "Generation" }
                    </abbr>
                    { ": " }
                    { self.gen }
                    <button class="mui-btn mui-btn--small btn-tiny"
                        disabled=self.gen == 0
                        onclick=self.link.callback(|_| Msg::DecGen)>
                        <i class="fas fa-minus"></i>
                    </button>
                    <button class="mui-btn mui-btn--small btn-tiny"
                        disabled=self.gen == self.config.period - 1
                        onclick=self.link.callback(|_| Msg::IncGen)>
                        <i class="fas fa-plus"></i>
                    </button>
                </li>
                <li>
                    <abbr title="Number of known living cells in the current generation. \
                        For Generations rules, dying cells are not counted.">
                        { "Cell count" }
                    </abbr>
                    { ": " }
                    { self.cells }
                </li>
                <li>
                    {
                        match self.status {
                            Status::Initial => "",
                            Status::Found => "Found a result.",
                            Status::None => "No more result.",
                            Status::Searching => "Searching...",
                            Status::Paused => "Paused.",
                        }
                    }
                </li>
            </ul>
        }
    }

    fn buttons(&self) -> Html {
        html! {
            <div class="buttons">
                <button class="mui-btn mui-btn--raised"
                    disabled=self.status == Status::Searching
                    onclick=self.link.callback(|_| Msg::Start)>
                    <i class="fas fa-play"></i>
                    <span class="mui--hidden-xs">
                        { "Start" }
                    </span>
                </button>
                <button class="mui-btn mui-btn--raised"
                    disabled=self.status != Status::Searching
                    onclick=self.link.callback(|_| Msg::Pause)>
                    <i class="fas fa-pause"></i>
                    <span class="mui--hidden-xs">
                        { "Pause" }
                    </span>
                </button>
                <button class="mui-btn mui-btn--raised"
                    disabled=self.status == Status::Searching
                    onclick=self.link.callback(|_| Msg::Reset)>
                    <i class="fas fa-redo"></i>
                    <span class="mui--hidden-xs">
                        <abbr title="Reset the world.">
                            { "Reset" }
                        </abbr>
                    </span>
                </button>
                <div class="mui--visible-xs-block"></div>
                <button class="mui-btn mui-btn--raised"
                    disabled=self.status == Status::Searching
                    onclick=self.link.callback(|_| Msg::Save)>
                    <i class="fas fa-save"></i>
                    <span class="mui--hidden-xs">
                        <abbr title="Save the search status in a json file.">
                            { "Save" }
                        </abbr>
                    </span>
                </button>
                <button class="mui-btn mui-btn--raised"
                    onclick=self.link.callback(|_| {
                        click_button("load").unwrap();
                        Msg::None
                    })>
                    <i class="fas fa-file-import"></i>
                    <span class="mui--hidden-xs">
                        <abbr title="Load the search status from a json file.">
                            { "Load" }
                        </abbr>
                    </span>
                </button>
                <input id="load"
                    type="file"
                    hidden=true
                    onchange=self.link.callback(|e| match e {
                        ChangeData::Files(files) => Msg::Load(files),
                        _ => Msg::None,
                    })/>
            </div>
        }
    }
}

fn download(text: &str, name: &str, mime: &str) -> Result<(), JsValue> {
    let a = HtmlAnchorElement::from(JsValue::from(
        web_sys::window()
            .ok_or(JsValue::UNDEFINED)?
            .document()
            .ok_or(JsValue::UNDEFINED)?
            .create_element("a")?,
    ));
    a.set_download(name);

    let array = Array::new();
    array.push(&JsValue::from_str(text));

    let blob = Blob::new_with_str_sequence_and_options(&array, BlobPropertyBag::new().type_(mime))?;

    a.set_href(&Url::create_object_url_with_blob(&blob)?);
    a.click();
    Url::revoke_object_url(&a.href())
}

fn click_button(id: &str) -> Result<(), JsValue> {
    let button = HtmlElement::from(JsValue::from(
        web_sys::window()
            .ok_or(JsValue::UNDEFINED)?
            .document()
            .ok_or(JsValue::UNDEFINED)?
            .get_element_by_id(id)
            .ok_or(JsValue::UNDEFINED)?,
    ));
    button.click();
    Ok(())
}
