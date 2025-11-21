package controller.utente;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.Mockito.*;

class ModificaDatiServletTest {
    private ModificaDatiServlet servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private UtenteDAO utenteDAOMock;
    private Utente utenteMock;
    private List<String> telefoniList;

    @BeforeEach
    void setUp() {
        servletUnderTest = new ModificaDatiServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        utenteDAOMock = mock(UtenteDAO.class);
        utenteMock = mock(Utente.class);
        telefoniList = new ArrayList<>();

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utenteMock);
        when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
        // return same mutable list when getTelefoni() called
        when(utenteMock.getTelefoni()).thenReturn(telefoniList);

        servletUnderTest.setUtenteDAO(utenteDAOMock);
    }

    @Test
    void testDoGet_MissingParams_ForwardsToError() throws ServletException, IOException {
        when(request.getParameter("nomeUtente")).thenReturn(null);
        when(request.getParameterValues("telefono")).thenReturn(null);

        servletUnderTest.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/errorForm.jsp");
        verify(dispatcher).forward(request, response);
        verifyNoInteractions(utenteDAOMock);
    }

    @Test
    void testDoGet_UpdateSuccess_CallsUpdateAndForwards() throws ServletException, IOException {
        when(request.getParameter("nomeUtente")).thenReturn("NuovoNome");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"12345"});

        // utenteMock.getTelefoni() returns telefoniList (initially empty)
        servletUnderTest.doGet(request, response);

        // telefono should have been added
        assert telefoniList.contains("12345");
        // updateUtente should be invoked with the mock utente
        verify(utenteDAOMock).updateUtente(utenteMock);
        // session attribute should be updated
        verify(session).setAttribute("utente", utenteMock);
        // forwarded to support page
        verify(request).getRequestDispatcher("modifica-dati-supporto");
        verify(dispatcher).forward(request, response);
    }
}
