library.vo library.glob library.v.beautified library.required_vo: library.v 
library.vio: library.v 
library.vos library.vok library.required_vos: library.v 
mini_functional_language.vo mini_functional_language.glob mini_functional_language.v.beautified mini_functional_language.required_vo: mini_functional_language.v library.vo
mini_functional_language.vio: mini_functional_language.v library.vio
mini_functional_language.vos mini_functional_language.vok mini_functional_language.required_vos: mini_functional_language.v library.vos
