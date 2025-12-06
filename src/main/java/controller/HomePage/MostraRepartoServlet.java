package controller.HomePage;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import model.utenteService.Utente;

import java.io.IOException;
import java.util.List;

@WebServlet("/mostra-reparto")
public class MostraRepartoServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        if(Validator.checkIfUserAdmin((Utente) request.getSession().getAttribute("utente"))) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException e) {
                log("Errore durante il forward verso /WEB-INF/results/admin/homepageAdmin.jsp", e);

            } catch (IOException e) {
                log("Errore di I/O durante il forward verso /WEB-INF/results/admin/homepageAdmin.jsp", e);

            }
            return;
        }
        String idParam = request.getParameter("id");
        int idReparto;

        try {
            idReparto = Integer.parseInt(idParam);
        } catch (NumberFormatException ex) {
            log("Parametro 'id' non valido: " + idParam, ex);
            RequestDispatcher dispatcher=request.getRequestDispatcher("/WEB-INF/errorJsp/ErroreReparto.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException | IOException e) {
                log("Errore durante il forward verso /WEB-INF/errorJsp/ErroreReparto.jsp", e);
            }
            return;
        }

        String position = request.getParameter("position");
        String address="/WEB-INF/results/reparto.jsp";

        Reparto reparto = null;
        List<Reparto> reparti = (List<Reparto>) getServletContext().getAttribute("reparti");
        for(Reparto r : reparti) {
            if(r.getIdReparto() == idReparto) {
                reparto = r;
            }
        }

        if (reparto != null) {
            request.setAttribute("reparto", reparto);

            HttpSession session = request.getSession();
            session.setAttribute("repartoAttuale", idReparto);
            if (position != null) {
                address += "#"+position;
            }
        } else {
            request.setAttribute("repartoNonTrovato", true);
            RequestDispatcher dispatcher=request.getRequestDispatcher("/WEB-INF/errorJsp/ErroreReparto.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException e) {
                log("Errore durante il forward verso /WEB-INF/errorJsp/ErroreReparto.jsp", e);

            } catch (IOException e) {
                log("Errore di I/O durante il forward verso /WEB-INF/errorJsp/ErroreReparto.jsp", e);

            }
            return;
        }

        RequestDispatcher dispatcher = request.getRequestDispatcher(address);
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward", e);

        } catch (IOException e) {
            log("Errore di I/O durante il forward", e);

        }
    }
}


