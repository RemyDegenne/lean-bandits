import VersoBlog

open Verso Genre Blog Site Output Html Template Theme

open Verso Doc Elab
open Lean

structure LightboxArgs where
  alt : String
  thumb : String
  full : String

section
open ArgParse
variable [Monad m] [MonadError m]
instance : FromArgs LightboxArgs m where
  fromArgs := LightboxArgs.mk <$>
    .named `alt .string false "Alt text" <*>
    .named `thumb .string false "Thumbnail URL" <*>
    .named `full .string false "Full URL"
end

open Verso Output Html in
inline_component Inline.lightbox (alt thumb full : String) where
  toHtml _ _ _ _ := do
    return {{<a href={{full}} class="glightbox"><img src={{thumb}} alt={{alt}}/></a>}}

@[role]
def lightbox : RoleExpanderOf LightboxArgs
  | { alt, thumb, full }, _ =>
    ``(Inline.lightbox $(quote alt) $(quote thumb) $(quote full) #[])
