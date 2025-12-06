package controller.utente;

import controller.utils.ControlMethod;
import controller.utils.Validator;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.Carrello;
import model.carrelloService.CarrelloDAO;
import model.carrelloService.RigaCarrello;
import model.carrelloService.RigaCarrelloDAO;
import model.libroService.Libro;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import model.utenteService.Utente;
import model.wishList.WishList;
import model.wishList.WishListDAO;

import java.io.IOException;
import java.util.List;

@WebServlet("/log-out")
public class LogoutServlet extends HttpServlet {
    // Allow dependency injection for testing
    private model.carrelloService.CarrelloDAO carrelloDAO;
    private model.wishList.WishListDAO wishListDAO;
    private model.carrelloService.RigaCarrelloDAO rigaCarrelloDAO;
    private model.libroService.RepartoDAO repartoDAO;

    public void setCarrelloDAO(model.carrelloService.CarrelloDAO carrelloDAO) { this.carrelloDAO = carrelloDAO; }
    public void setWishListDAO(model.wishList.WishListDAO wishListDAO) { this.wishListDAO = wishListDAO; }
    public void setRigaCarrelloDAO(model.carrelloService.RigaCarrelloDAO rigaCarrelloDAO) { this.rigaCarrelloDAO = rigaCarrelloDAO; }
    public void setRepartoDAO(model.libroService.RepartoDAO repartoDAO) { this.repartoDAO = repartoDAO; }
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        HttpSession session = request.getSession();
    CarrelloDAO carrelloDAO = (this.carrelloDAO != null) ? this.carrelloDAO : new CarrelloDAO();
    WishListDAO wishListDAO = (this.wishListDAO != null) ? this.wishListDAO : new WishListDAO();
        Utente utente = (Utente) session.getAttribute("utente");

        // If user is an admin (Gestore) we only refresh reparti in the servlet context
        // and do not touch cart/wishlist persistence since admins don't have them.
        if (utente != null && Validator.checkIfUserAdmin(utente)) {
            getServletContext().removeAttribute("reparti");
            RepartoDAO service = (this.repartoDAO != null) ? this.repartoDAO : new RepartoDAO();
            List<Reparto> reparti = service.doRetrivedAll();
            getServletContext().setAttribute("reparti", reparti);
            session.invalidate();
            ControlMethod.safeRedirect(response, "index.html", this);
            return;
        }

        Carrello carrello = (Carrello) session.getAttribute("carrello");
        WishList wishList = (WishList) session.getAttribute("wishList");
        if (wishList != null && utente != null) {
            wishList.setEmail(utente.getEmail());
        }

        try{
            RigaCarrelloDAO rigaCarrelloService = (this.rigaCarrelloDAO != null) ? this.rigaCarrelloDAO : new RigaCarrelloDAO();
            if(carrelloDAO.doRetriveByUtente(utente.getEmail()) != null && !(carrelloDAO.doRetriveByUtente(utente.getEmail()).getRigheCarrello().isEmpty())) {
                //Carrello carrello2=carrelloDAO.doRetriveByUtente(utente.getEmail());
                rigaCarrelloService.deleteRigheCarrelloByIdCarrello(carrelloDAO.doRetriveByUtente(utente.getEmail()).getIdCarrello());//elimino ciò che è presente nel db
            }
            WishListDAO wishListService = (this.wishListDAO != null) ? this.wishListDAO : new WishListDAO();
            if(wishListDAO.doRetrieveByEmail(utente.getEmail())!= null && !(wishListDAO.doRetrieveByEmail(utente.getEmail()).getLibri().isEmpty())) {
                wishListService.deleteWishListByEmail(utente.getEmail());//elimino ciò che è presente nel db
            }

            if(carrello != null && carrello.getRigheCarrello()!= null) {
                for (RigaCarrello riga : carrello.getRigheCarrello())
                    rigaCarrelloService.doSave(riga); //ripopolo il db con le informazioni presenti in sessione
            }
            if(wishList != null && wishList.getLibri()!= null) {
                for (Libro libro : wishList.getLibri()) {
                    wishListService.doSave(wishList, libro.getIsbn()); //ripopolo il db con le informazioni presenti in sessione
                }
            }


        } catch (Exception e) {
            ControlMethod.safeSendError(response, HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "Si è verificato un errore interno", this);
            return;
        }

        //Se l'admin modifica i reparti è necessario apportare modifiche alla lista salvata del serveltContext
        if(Validator.checkIfUserAdmin(utente)){
            getServletContext().removeAttribute("reparti");
            RepartoDAO service = (this.repartoDAO != null) ? this.repartoDAO : new RepartoDAO();
            List<Reparto> reparti = service.doRetrivedAll();
            getServletContext().setAttribute("reparti", reparti);
        }
        session.invalidate();
        ControlMethod.safeRedirect(response, "index.html", this);
    }
}
